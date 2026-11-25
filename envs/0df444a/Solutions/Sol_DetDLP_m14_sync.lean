-- Prove2me | solution 1 for DetDLP.m14_sync
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T07:46:28.052853+00:00
-- url     : https://prove2.me/submissions/3d704d4e-175d-4e14-a3b1-c1abd0718cab

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_padded_tree_rank_walker_v2_machine

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace DetDLP.D4SoloSync

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4GuardTree.Expansion DetDLP.D4SoloRaw DetDLP.D4SoloNode
open DetDLP.D4SoloRoot DetDLP.D4SoloStep DetDLP.D4SoloStepEq DetDLP.D4SoloTree
open DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable section

section Helpers

theorem residue_eq_residue_lift {f : ℤ[X]} (hf : f.Monic)
    (l : ℕ) {p₁ p₂ : ℕ} (hp : p₁ ≤ p₂) (z : B f l p₁) :
    residue f l p₁ hf z = residue f l p₂ hf (lift hf p₂ z) :=
  ((DetDLP.d4_residue_lift_eq f l p₁ p₂ hf hp).1 z).symm

theorem sum_map_ofFn_const {α : Type} (n c : ℕ) (fn : Fin n → α) (g : α → ℕ)
    (hg : ∀ i, g (fn i) = c) : ((List.ofFn fn).map g).sum = n * c := by
  have hmap : (List.ofFn fn).map g = List.replicate n c :=
    List.ext_getElem (by simp) (fun i h1 _ => by simp [hg])
  rw [hmap, List.sum_replicate, smul_eq_mul]

theorem prod_map_ofFn {α β : Type} [CommMonoid β] (n : ℕ) (fn : Fin n → α) (g : α → β) :
    ((List.ofFn fn).map g).prod = ∏ i : Fin n, g (fn i) := by
  rw [Fin.prod_univ_def]
  congr 1
  exact List.ext_getElem (by simp) (fun i h1 _ => by simp)

private theorem choice_congr {α : Type} {n₁ n₂ : ℕ} {f₁ : Fin n₁ → D4RankCode.Tree α}
    {f₂ : Fin n₂ → D4RankCode.Tree α} (hn : n₁ = n₂)
    (hf : ∀ d : Fin n₁, f₁ d = f₂ (d.cast hn)) :
    D4RankCode.Tree.choice n₁ f₁ = D4RankCode.Tree.choice n₂ f₂ := by
  subst hn; congr 1; funext d; exact hf d

theorem active_children_remSlots {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ} (k : ℕ)
    {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd)
    (sub : (ν : Branch cert.s) → (g : Fin 64) →
      SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc k (cert.childNode ν g))
    (ν : Branch cert.s)
    (tail : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    remSlots ((List.ofFn fun g : Fin 64 =>
      (⟨k, cert.childNode ν g, sub ν g⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) ++ tail) =
      64 * D4GuardTree.slots k + remSlots tail := by
  unfold remSlots
  rw [List.map_append, List.sum_append, List.map_ofFn]
  have hmap : List.ofFn ((fun it : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc =>
      D4GuardTree.slots it.1) ∘
      fun g : Fin 64 => (⟨k, cert.childNode ν g, sub ν g⟩ :
        WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) =
      List.replicate 64 (D4GuardTree.slots k) :=
    List.ext_getElem (by simp) (fun i hi _ => by simp)
  rw [hmap, List.sum_replicate, smul_eq_mul]

private theorem active_children_remLeaves {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ} (k : ℕ)
    {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd)
    (sub : (ν : Branch cert.s) → (g : Fin 64) →
      SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc k (cert.childNode ν g))
    (ν : Branch cert.s)
    (tail : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    remLeaves ((List.ofFn fun g : Fin 64 =>
      (⟨k, cert.childNode ν g, sub ν g⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) ++ tail) =
      64 ^ (k + 1) + remLeaves tail := by
  unfold remLeaves
  rw [List.map_append, List.sum_append, List.map_ofFn]
  have hmap : List.ofFn ((fun it : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc =>
      64 ^ it.1) ∘
      fun g : Fin 64 => (⟨k, cert.childNode ν g, sub ν g⟩ :
        WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) =
      List.replicate 64 (64 ^ k) :=
    List.ext_getElem (by simp) (fun i hi _ => by simp)
  rw [hmap, List.sum_replicate, smul_eq_mul, ← pow_succ']

private theorem active_hp_le_guard {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd) :
    nd.pCurr + AppendixD4.loss nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) 0 ≤
      totalGuard x.S (Nat.clog 32 (4 * x.m)) + x.p := by
  have hp_curr_le : nd.pCurr ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d := by
    refine nd.hp_le.trans ?_
    split_ifs with h0
    · exact Nat.le_add_right _ _
    · exact Nat.add_le_add_left (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (shift_mono_solo x.S (Nat.sub_le nd.d 1)))) _
  exact step_prec_le_guard x.S (Nat.clog 32 (4 * x.m)) x.p nd.d nd.pCurr nd.G.nE
    cert.hd cert.hM_le cert.hu_pos hp_curr_le

private theorem active_ask_eq {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ} (guard : ℕ)
    {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd) (j : ℕ) :
    ask (contextV2 x.S x.m x.p guard x.l (polynomialBits f)) nd.toWorkItem.bits j =
      D4NodeQuery.request nd.G nd.host (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d)
        nd.pCurr x.l f j := by
  have h1 := (DetDLP.d4_padded_tree_rank_walker_v2_machine M_node o_node).1
    x.S x.m x.p guard x.l f nd.toWorkItem j cert.hd
  rw [h1]
  have hlist : (List.ofFn fun v : Fin nd.toWorkItem.pins.length => (nd.toWorkItem.pins.get v).2.val) =
      (List.ofFn fun v : Fin nd.pins.length => (nd.host v).val) := by
    apply List.ext_getElem
    · simp [SoloNode.toWorkItem]
    · intro idx h₁ h₂
      simp [SoloNode.toWorkItem, SoloNode.host]
  unfold D4NodeQuery.request D2.input
  dsimp only [SoloNode.toWorkItem] at hlist ⊢
  rw [hlist]

private theorem callsV2_step_cons (ctx : Wd) (F : Wd → WalkerStep) (fuel : ℕ)
    (todo done_ : List Wd) (i : Wd) (tail : List Wd) (b u : ℕ) (acc : Wd) (lossSum : ℕ)
    (hdrop : todo.drop ((todo.map (small ctx)).idxOf false) = i :: tail) :
    callsV2 ctx F (fuel + 1) todo done_ b u acc lossSum =
      let done' := done_ ++ todo.take ((todo.map (small ctx)).idxOf false)
      let s := F i; let w := D4RankWalker.digitWidth s.n; let d := u % 2 ^ w
      let count : Call := (phaseStateV2 [true] ctx (i :: tail) done' b u acc lossSum, ask ctx i 0, countWord s.n)
      if w ≤ b then if hd : d < s.n then
        let ans := s.branch ⟨d, hd⟩
        count :: (phaseStateV2 [false] ctx (i :: tail) done' (b - w) (u / 2 ^ w) acc lossSum, ask ctx i (d + 1), ans) ::
          callsV2 ctx F fuel (children i ans ++ tail) done' (b - w) (u / 2 ^ w) (productV2 ctx acc ans) (lossSum + stepLoss ctx i)
      else [count] else [count] := by
  rw [callsV2.eq_def]
  dsimp only
  rw [hdrop]

end Helpers

section SyncTheorems

/-- (1) Exact bit-level tree equality between `unrollCertFuel` and `unrollAuxV2`. -/
theorem unrollCertFuel_bits_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (hRing : RingOK f)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ) :
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let F := soloStepFn M_node o_node ctx
    ∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      remSlots todo ≤ fuel →
      treeMap (SoloLeafData.toBits ctx)
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum) =
      unrollAuxV2 ctx F fuel ((todoNodes todo).map (·.toWorkItem.bits))
        (done.map (·.toWorkItem.bits)) (residue f x.l (guard + x.p) hf accVal) lossSum := by
  intro D guard ctx F fuel
  induction fuel with
  | zero =>
    intro todo done accVal lossSum hfuel
    have hrem0 : (peelCert todo).2 = [] := by
      rcases peelCert_rem_shape todo with h0 | ⟨k, nd, cert, sub, tail, hr⟩
      · exact h0
      · exfalso
        have hle := (peelCert_remSlots_le todo).trans hfuel
        rw [hr] at hle
        simp only [remSlots, List.map_cons, D4GuardTree.slots, List.sum_cons] at hle
        omega
    obtain ⟨htake, hdrop⟩ := peelCert_bits_split guard todo
    have hdrop0 : ((todoNodes todo).map (·.toWorkItem.bits)).drop
        ((((todoNodes todo).map (·.toWorkItem.bits)).map (small ctx)).idxOf false) = [] := by
      rw [← hdrop, hrem0]; rfl
    simp only [unrollCertFuel, treeMap, SoloLeafData.toBits, List.map_append]
    conv_rhs => rw [unrollAuxV2.eq_1]
    rw [hdrop0, ← htake]
  | succ fuel ih =>
    intro todo done accVal lossSum hfuel
    obtain ⟨htake, hdrop⟩ := peelCert_bits_split guard todo
    rcases peelCert_rem_shape todo with hempty | ⟨k, nd, cert, sub, tail, hrem⟩
    · simp only [unrollCertFuel, hempty, treeMap, SoloLeafData.toBits, List.map_append]
      conv_rhs => rw [unrollAuxV2.eq_1]
      have hdrop0 : ((todoNodes todo).map (·.toWorkItem.bits)).drop
          ((((todoNodes todo).map (·.toWorkItem.bits)).map (small ctx)).idxOf false) = [] := by
        rw [← hdrop, hempty]; rfl
      rw [hdrop0, ← htake]
    · simp only [unrollCertFuel, hrem, treeMap]
      conv_rhs => rw [unrollAuxV2.eq_1]
      have hdrop_cons : ((todoNodes todo).map (·.toWorkItem.bits)).drop
          ((((todoNodes todo).map (·.toWorkItem.bits)).map (small ctx)).idxOf false) =
          nd.toWorkItem.bits :: (todoNodes tail).map (·.toWorkItem.bits) := by
        rw [← hdrop, hrem]; rfl
      rw [hdrop_cons, ← htake, ← List.map_append]
      dsimp only
      have hask0 := active_ask_eq guard cert 0
      have hrun0 := cert.hrun0
      dsimp only at hrun0
      rw [← hask0] at hrun0
      have hn_eq : (F nd.toWorkItem.bits).n = cert.nBranches := soloStepFn_n_eq hrun0
      refine choice_congr hn_eq.symm (fun d => ?_)
      let ν := cert.order d
      have hask_d := active_ask_eq guard cert (d.val + 1)
      have hrund := cert.hrun_br d
      dsimp only at hrund
      rw [← hask_d] at hrund
      have hbr : (F nd.toWorkItem.bits).branch (d.cast hn_eq.symm) = cert.s.bits hf ν :=
        soloStepFn_branch_eq hrun0 (d.cast hn_eq.symm) hrund
      rw [hbr]
      have hch_eq : children nd.toWorkItem.bits (cert.s.bits hf ν) =
          List.ofFn (fun g : Fin 64 => (cert.childNode ν g).toWorkItem.bits) :=
        (childSoloNode_children_eq x hf E_pkt o_pkt K_loc nd cert.s rfl cert.hbal cert.hM_le
          cert.hinc_le cert.hpkt_eval cert.hdeg_f cert.hu_pos cert.hu_le_M ν).symm
      let loss₀ := AppendixD4.loss nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) 0
      let w_val : B f x.l (guard + x.p) :=
        lift hf (guard + x.p) (AdjoinRoot.of _ (cert.s.weight ν.1 ν.2.1) : B f x.l (nd.pCurr + loss₀))
      have hp_le : nd.pCurr + loss₀ ≤ guard + x.p := active_hp_le_guard cert
      have hans_fld : fld (cert.s.bits hf ν) 1 = residue f x.l (guard + x.p) hf w_val := by
        have hfld1 : fld (cert.s.bits hf ν) 1 =
            residue f x.l (nd.pCurr + loss₀) hf (AdjoinRoot.of _ (cert.s.weight ν.1 ν.2.1)) := by
          unfold Step.bits
          simp [loss₀]
        rw [hfld1]
        exact residue_eq_residue_lift hf x.l hp_le _
      have hprod : productV2 ctx (residue f x.l (guard + x.p) hf accVal) (cert.s.bits hf ν) =
          residue f x.l (guard + x.p) hf (accVal * w_val) :=
        productV2_eq_residue_mul x.S x.m x.p guard x.l f hf hRing x.hl
          (Nat.add_pos_right _ x.hp) _ _ accVal w_val rfl hans_fld
      have hsloss : stepLoss ctx nd.toWorkItem.bits = loss₀ := stepLoss_ctx_eq guard nd cert.hd
      let chList : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :=
        List.ofFn fun g : Fin 64 => ⟨k, cert.childNode ν g, sub ν g⟩
      have htodo_next : ((todoNodes (chList ++ tail)).map (·.toWorkItem.bits)) =
          children nd.toWorkItem.bits (cert.s.bits hf ν) ++ (todoNodes tail).map (·.toWorkItem.bits) := by
        rw [hch_eq]
        simp only [todoNodes, chList, List.map_append, List.ofFn_eq_map, List.map_map]
        rfl
      have hrs_peel : 1 + 64 * D4GuardTree.slots k + remSlots tail ≤ remSlots todo := by
        have h1 := peelCert_remSlots_le todo
        rw [hrem] at h1
        simpa [remSlots, D4GuardTree.slots, Nat.add_assoc] using h1
      have hrs_next : remSlots (chList ++ tail) ≤ fuel := by
        rw [active_children_remSlots k cert sub ν tail]; omega
      rw [ih _ _ _ _ hrs_next, htodo_next, hprod, hsloss]

/-- (2) Every leaf emitted by `unrollCertFuel` (with `fuel ≥ remSlots todo`) satisfies `SoloLeafData.Valid`. -/
theorem unrollCertFuel_all_valid {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ) :
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    ∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      remSlots todo ≤ fuel →
      lossSum + localAllowance x.S D * remSlots todo ≤ guard →
      done.length + remLeaves todo ≤ 64 ^ D →
      (∀ m ∈ done, D ≤ m.d ∨ m.G.nE ≤ D3Stopped.threshold x.S) →
      List.Perm (pinFirsts (done ++ todoNodes todo)) (List.finRange (4 * x.m * x.k)) →
      treeAll SoloLeafData.Valid
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum) := by
  intro D guard fuel
  induction fuel with
  | zero =>
    intro todo done accVal lossSum hfuel hloss hdone hstop hperm
    have hrem0 : (peelCert todo).2 = [] := by
      rcases peelCert_rem_shape todo with h0 | ⟨k, nd, cert, sub, tail, hr⟩
      · exact h0
      · exfalso
        have hle := (peelCert_remSlots_le todo).trans hfuel
        rw [hr] at hle
        simp only [remSlots, List.map_cons, D4GuardTree.slots, List.sum_cons] at hle
        omega
    have hnodes : todoNodes todo = (peelCert todo).1 := by
      have hn := (peelCert_nodes_eq todo).symm
      rw [hrem0] at hn
      simpa [todoNodes] using hn
    simp only [unrollCertFuel, treeAll, SoloLeafData.Valid]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · have hrl := peelCert_remLeaves_le todo
      dsimp only [D] at hdone
      rw [List.length_append]; omega
    · intro m hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact hstop m h1
      · exact peelCert_stopped todo m h2
    · rw [← hnodes]; exact hperm
  | succ fuel ih =>
    intro todo done accVal lossSum hfuel hloss hdone hstop hperm
    rcases peelCert_rem_shape todo with hrem0 | ⟨k, nd, cert, sub, tail, hrem⟩
    · have hnodes : todoNodes todo = (peelCert todo).1 := by
        have hn := (peelCert_nodes_eq todo).symm
        rw [hrem0] at hn
        simpa [todoNodes] using hn
      simp only [unrollCertFuel, hrem0, treeAll, SoloLeafData.Valid]
      refine ⟨by omega, ?_, ?_, ?_⟩
      · have hrl := peelCert_remLeaves_le todo
        dsimp only [D] at hdone
        rw [List.length_append]; omega
      · intro m hm
        rcases List.mem_append.mp hm with h1 | h2
        · exact hstop m h1
        · exact peelCert_stopped todo m h2
      · rw [← hnodes]; exact hperm
    · simp only [unrollCertFuel, hrem, treeAll]
      intro d
      let ν := cert.order d
      let chList : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :=
        List.ofFn fun g : Fin 64 => ⟨k, cert.childNode ν g, sub ν g⟩
      have hrs_peel : 1 + 64 * D4GuardTree.slots k + remSlots tail ≤ remSlots todo := by
        have h1 := peelCert_remSlots_le todo
        rw [hrem] at h1
        simpa [remSlots, D4GuardTree.slots, Nat.add_assoc] using h1
      have hrs_next : remSlots (chList ++ tail) = 64 * D4GuardTree.slots k + remSlots tail :=
        active_children_remSlots k cert sub ν tail
      have hrl_peel : (peelCert todo).1.length + (64 ^ (k + 1) + remLeaves tail) ≤ remLeaves todo := by
        have h1 := peelCert_remLeaves_le todo
        rw [hrem] at h1
        simpa [remLeaves] using h1
      have hrl_next : remLeaves (chList ++ tail) = 64 ^ (k + 1) + remLeaves tail :=
        active_children_remLeaves k cert sub ν tail
      have hloss₀_le : AppendixD4.loss nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) 0 ≤
          localAllowance x.S D :=
        loss_le_localAllowance x.S D nd.d nd.G.nE cert.hd.le cert.hM_le cert.hu_pos
      apply ih
      · rw [hrs_next]; omega
      · rw [hrs_next]
        have hmul_le : localAllowance x.S D * (1 + (64 * D4GuardTree.slots k + remSlots tail)) ≤
            localAllowance x.S D * remSlots todo :=
          Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_add, Nat.mul_one] at hmul_le
        omega
      · rw [List.length_append, hrl_next]; omega
      · intro m hm
        rcases List.mem_append.mp hm with h1 | h2
        · exact hstop m h1
        · exact peelCert_stopped todo m h2
      · have hp_ch : List.Perm (pinFirsts (todoNodes chList)) (nd.pins.map Prod.fst) := by
          have htn : todoNodes chList = List.ofFn (fun g : Fin 64 => cert.childNode ν g) := by
            simp only [todoNodes, chList, List.ofFn_eq_map, List.map_map]
            rfl
          rw [htn]; exact childPins_pinFirsts_perm cert ν
        have hpf_split : ∀ a b : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)),
            pinFirsts (a ++ b) = pinFirsts a ++ pinFirsts b := by
          intro a b; simp [pinFirsts, List.flatMap_append]
        have htn_app : todoNodes (chList ++ tail) = todoNodes chList ++ todoNodes tail := by
          simp [todoNodes]
        have hnodes_eq : (peelCert todo).1 ++ (nd :: todoNodes tail) = todoNodes todo := by
          have hn := peelCert_nodes_eq todo
          rw [hrem] at hn
          exact hn
        rw [List.append_assoc, htn_app, hpf_split, hpf_split, hpf_split]
        refine (List.Perm.append_left _ (List.Perm.append_left _ (hp_ch.append_right _))).trans ?_
        have hrew : pinFirsts done ++ (pinFirsts (peelCert todo).1 ++ (nd.pins.map Prod.fst ++ pinFirsts (todoNodes tail))) =
            pinFirsts (done ++ todoNodes todo) := by
          rw [← hnodes_eq]
          simp [pinFirsts, List.flatMap_append]
        rw [hrew]; exact hperm

/-- Helper: peeling stopped nodes from `todo` preserves `D4UnrollBudget.Work`. -/
private theorem work_of_peelCert {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ} {α : Type} (D K : ℕ)
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
    (hD : D = Nat.clog 32 (4 * x.m))
    (t : D4RankCode.Tree α)
    (hw : D4UnrollBudget.Work x.S D K ((todoNodes (peelCert todo).2).map fun nd => (nd.d, nd.G.nE)) t) :
    D4UnrollBudget.Work x.S D K ((todoNodes todo).map fun nd => (nd.d, nd.G.nE)) t := by
  induction todo with
  | nil => exact hw
  | cons it rest ih =>
    rcases it with ⟨k, nd, u⟩
    cases k with
    | zero =>
      rcases u with ⟨hs⟩
      exact D4UnrollBudget.Work.stop (hD ▸ hs) (ih hw)
    | succ k =>
      cases u with
      | inl hs_box =>
        rcases hs_box with ⟨hs⟩
        exact D4UnrollBudget.Work.stop (hD ▸ hs) (ih hw)
      | inr _ => exact hw

private theorem branch_count_bound {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd) :
    (cert.nBranches : ℝ) ≤
      ((2 ^ (D3Stopped.shift x.S nd.d + 1) * points nd.G.nE (D3Stopped.shift x.S nd.d) : ℕ) : ℝ) *
        Real.exp (((8 * K_loc : ℕ) : ℝ) * nd.G.nE / Real.sqrt (D3Stopped.width x.S nd.d)) := by
  let a := D3Stopped.shift x.S nd.d
  let u := D3Stopped.width x.S nd.d
  let M := nd.G.nE
  let E_max := Real.exp (((8 * K_loc : ℕ) : ℝ) * M / Real.sqrt u)
  have hu_pos_r : (0 : ℝ) < u := by exact_mod_cast cert.hu_pos
  have hcard_eq : cert.nBranches = Fintype.card (Branch cert.s) :=
    (Fintype.card_fin cert.nBranches).symm.trans (Fintype.card_congr cert.order)
  have hsum_br : (Fintype.card (Branch cert.s) : ℝ) =
      ∑ t : Node a u, (points M a : ℝ) * ((cert.s.modes t).count : ℝ) := by
    have hc : Fintype.card (Branch cert.s) = ∑ t : Node a u, points M a * (cert.s.modes t).count := by
      simp only [Branch, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
      rfl
    rw [hc]; push_cast; rfl
  have hmode_le : ∀ t : Node a u, ((cert.s.modes t).count : ℝ) ≤ E_max := by
    intro t
    refine (cert.hmodes t).trans (Real.exp_le_exp.mpr ?_)
    have hdiv_nat := cert.hinc_prec (AppendixD4.level t.val) t.property.2
    have hmul_nat : (nd.pCurr + increase M a u (AppendixD4.level t.val)) * u ≤
        64 * M * tileScale a (AppendixD4.level t.val) :=
      (Nat.mul_le_mul_right u hdiv_nat).trans (Nat.div_mul_le_self _ _)
    have hmul_r : ((nd.pCurr : ℝ) + (increase M a u (AppendixD4.level t.val) : ℝ)) * (u : ℝ) ≤
        64 * (M : ℝ) * (tileScale a (AppendixD4.level t.val) : ℝ) := by
      exact_mod_cast hmul_nat
    have hts_pos : (0 : ℝ) < (tileScale a (AppendixD4.level t.val) : ℝ) := by
      unfold tileScale; positivity
    have hfrac_le : (M : ℝ) * (nd.pCurr + increase M a u (AppendixD4.level t.val)) /
        tileScale a (AppendixD4.level t.val) ≤ (8 * (M : ℝ) / Real.sqrt u) ^ 2 := by
      have hsq : (8 * (M : ℝ) / Real.sqrt u) ^ 2 = 64 * (M : ℝ) ^ 2 / u := by
        rw [div_pow, mul_pow, Real.sq_sqrt hu_pos_r.le]; ring
      rw [hsq, div_le_div_iff₀ hts_pos hu_pos_r]
      nlinarith [hmul_r, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    have hsqrt_le : Real.sqrt ((M : ℝ) * (nd.pCurr + increase M a u (AppendixD4.level t.val)) /
        tileScale a (AppendixD4.level t.val)) ≤ 8 * (M : ℝ) / Real.sqrt u := by
      refine (Real.sqrt_le_sqrt hfrac_le).trans ?_
      exact (Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 8 * (M : ℝ) / Real.sqrt u)).le
    calc (K_loc : ℝ) * Real.sqrt _
        ≤ (K_loc : ℝ) * (8 * (M : ℝ) / Real.sqrt u) :=
          mul_le_mul_of_nonneg_left hsqrt_le (Nat.cast_nonneg _)
      _ = ((8 * K_loc : ℕ) : ℝ) * M / Real.sqrt u := by push_cast; ring
  have hnode_card : Fintype.card (Node a u) ≤ 2 ^ (a + 1) := by
    calc Fintype.card (Node a u) ≤ Fintype.card (Fin (2 ^ (a + 1))) := Fintype.card_subtype_le _
      _ = 2 ^ (a + 1) := Fintype.card_fin _
  rw [hcard_eq, hsum_br]
  calc ∑ t : Node a u, (points M a : ℝ) * ((cert.s.modes t).count : ℝ)
      ≤ ∑ _ : Node a u, (points M a : ℝ) * E_max :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hmode_le t) (Nat.cast_nonneg _)
    _ = (Fintype.card (Node a u) : ℝ) * ((points M a : ℝ) * E_max) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ (a + 1) : ℕ) : ℝ) * ((points M a : ℝ) * E_max) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hnode_card) (by positivity)
    _ = ((2 ^ (a + 1) * points M a : ℕ) : ℝ) * E_max := by push_cast; ring

/-- (3) `unrollCertFuel` satisfies `D4UnrollBudget.Work`, hence `Tree.Fits (budget x.S D (8 * K_loc))`. -/
theorem unrollCertFuel_work {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc guard : ℕ) :
    let D := Nat.clog 32 (4 * x.m)
    ∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      remSlots todo ≤ fuel →
      D4UnrollBudget.Work x.S D (8 * K_loc)
        ((todoNodes todo).map fun nd => (nd.d, nd.G.nE))
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum) := by
  intro D fuel
  induction fuel with
  | zero =>
    intro todo done accVal lossSum hfuel
    have hrem0 : (peelCert todo).2 = [] := by
      rcases peelCert_rem_shape todo with h0 | ⟨k, nd, cert, sub, tail, hr⟩
      · exact h0
      · exfalso
        have hle := (peelCert_remSlots_le todo).trans hfuel
        rw [hr] at hle
        simp only [remSlots, List.map_cons, D4GuardTree.slots, List.sum_cons] at hle
        omega
    apply work_of_peelCert D (8 * K_loc) todo rfl
    rw [hrem0]
    exact D4UnrollBudget.Work.done _
  | succ fuel ih =>
    intro todo done accVal lossSum hfuel
    apply work_of_peelCert D (8 * K_loc) todo rfl
    rcases peelCert_rem_shape todo with hrem0 | ⟨k, nd, cert, sub, tail, hrem⟩
    · simp only [unrollCertFuel, hrem0, todoNodes, List.map_nil]
      exact D4UnrollBudget.Work.done _
    · simp only [unrollCertFuel, hrem, todoNodes, List.map_cons]
      refine D4UnrollBudget.Work.step cert.hd cert.hM (branch_count_bound cert)
        (fun i g => (cert.childNode (cert.order i) g).G.nE)
        (fun i => cert.s.mass (cert.order i).1 (cert.order i).2.1 (cert.order i).2.2)
        (fun i => ?_)
      have hrs_peel : 1 + 64 * D4GuardTree.slots k + remSlots tail ≤ remSlots todo := by
        have h1 := peelCert_remSlots_le todo
        rw [hrem] at h1
        simpa [remSlots, D4GuardTree.slots, Nat.add_assoc] using h1
      have hrs_next : remSlots ((List.ofFn fun g : Fin 64 =>
          (⟨k, cert.childNode (cert.order i) g, sub (cert.order i) g⟩ :
            WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) ++ tail) ≤ fuel := by
        rw [active_children_remSlots k cert sub (cert.order i) tail]; omega
      let loss₀ := AppendixD4.loss nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) 0
      let w_i : B f x.l (guard + x.p) :=
        lift hf (guard + x.p) (AdjoinRoot.of _ (cert.s.weight (cert.order i).1 (cert.order i).2.1) : B f x.l (nd.pCurr + loss₀))
      have hih := ih
        ((List.ofFn fun g : Fin 64 =>
          (⟨k, cert.childNode (cert.order i) g, sub (cert.order i) g⟩ :
            WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) ++ tail)
        (done ++ (peelCert todo).1) (accVal * w_i) (lossSum + loss₀) hrs_next
      have hmap_eq : ((todoNodes ((List.ofFn fun g : Fin 64 =>
          (⟨k, cert.childNode (cert.order i) g, sub (cert.order i) g⟩ :
            WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) ++ tail)).map
          fun m => (m.d, m.G.nE)) =
          (List.ofFn fun g : Fin 64 => (nd.d + 1, (cert.childNode (cert.order i) g).G.nE)) ++
            (todoNodes tail).map (fun m => (m.d, m.G.nE)) := by
        simp only [todoNodes, List.map_append, List.ofFn_eq_map, List.map_map]
        rfl
      rw [hmap_eq] at hih
      exact hih

/-- (4) Every oracle call in `callsV2` is covered by `CallCovered`. -/
theorem unrollCertFuel_calls {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (hRing : RingOK f)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc bBudget : ℕ) :
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let F := soloStepFn M_node o_node ctx
    ∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (b u : ℕ) (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      (∀ it ∈ todo, it.2.1.d + it.1 = D) →
      (∀ m ∈ done, m.d ≤ D) →
      lossSum + localAllowance x.S D * remSlots todo ≤ guard →
      done.length + remLeaves todo ≤ 64 ^ D →
      b ≤ bBudget →
      u < 2 ^ bBudget →
      ∀ e ∈ callsV2 ctx F fuel ((todoNodes todo).map (·.toWorkItem.bits))
        (done.map (·.toWorkItem.bits)) b u (residue f x.l (guard + x.p) hf accVal) lossSum,
      CallCovered x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard bBudget e := by
  intro D guard ctx F fuel
  have hlen_le_leaves : ∀ ts : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc),
      (todoNodes ts).length ≤ remLeaves ts := by
    intro ts
    induction ts with
    | nil => simp [todoNodes, remLeaves]
    | cons it rest ih_l =>
      unfold todoNodes remLeaves at ih_l
      have h1 : 1 ≤ 64 ^ it.1 := Nat.one_le_pow _ _ (by decide)
      simp only [todoNodes, remLeaves, List.map_cons, List.length_cons, List.sum_cons]
      omega
  induction fuel with
  | zero =>
    intro todo done b u accVal lossSum _ _ _ _ _ _ e he
    rw [callsV2.eq_def] at he
    dsimp only at he
    split at he
    · cases (by assumption : 0 = Nat.succ _)
    · cases he
  | succ fuel ih =>
    intro todo done b u accVal lossSum hdepth hdone_d hloss hdone_len hb hu e he
    obtain ⟨htake, hdrop⟩ := peelCert_bits_split guard todo
    rcases peelCert_rem_shape todo with hrem0 | ⟨k, nd, cert, sub, tail, hrem⟩
    · rw [callsV2.eq_def] at he
      dsimp only at he
      rw [← hdrop, hrem0] at he
      cases he
    · have hdrop_cons : ((todoNodes todo).map (·.toWorkItem.bits)).drop
          ((((todoNodes todo).map (·.toWorkItem.bits)).map (small ctx)).idxOf false) =
          nd.toWorkItem.bits :: (todoNodes tail).map (·.toWorkItem.bits) := by
        rw [← hdrop, hrem]; rfl
      rw [callsV2_step_cons _ _ _ _ _ _ _ _ _ _ _ hdrop_cons, ← htake, ← List.map_append] at he
      dsimp only at he
      have hask0 := active_ask_eq guard cert 0
      have hrun0 := cert.hrun0
      dsimp only at hrun0
      rw [← hask0] at hrun0
      have hn_eq : (F nd.toWorkItem.bits).n = cert.nBranches := soloStepFn_n_eq hrun0
      have hpend_d : ∀ m ∈ nd :: todoNodes tail, m.d ≤ D := by
        intro m hm
        have hsub_nodes : m ∈ todoNodes todo := by
          have hn := peelCert_nodes_eq todo
          rw [hrem] at hn
          rw [← hn]
          exact List.mem_append_right _ hm
        obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hsub_nodes
        have hd_eq := hdepth it hit; omega
      have hdone'_d : ∀ m ∈ done ++ (peelCert todo).1, m.d ≤ D := by
        intro m hm
        rcases List.mem_append.mp hm with h1 | h2
        · exact hdone_d m h1
        · have hsub_nodes : m ∈ todoNodes todo := by
            rw [← peelCert_nodes_eq todo]
            exact List.mem_append_left _ h2
          obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hsub_nodes
          have hd_eq := hdepth it hit; omega
      have htot_len : (nd :: todoNodes tail).length + (done ++ (peelCert todo).1).length ≤ 64 ^ D := by
        have hrl_p := peelCert_remLeaves_le todo
        rw [hrem] at hrl_p
        have htl := hlen_le_leaves tail
        have h1 : 1 ≤ 64 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
        simp only [remLeaves, List.map_cons, List.sum_cons] at hrl_p
        simp only [List.length_cons, List.length_append]
        dsimp only [D] at hdone_len ⊢
        unfold remLeaves at htl hdone_len
        omega
      have hcnt_cov : CallCovered x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard bBudget
          (phaseStateV2 [true] ctx (nd.toWorkItem.bits :: (todoNodes tail).map (·.toWorkItem.bits))
            ((done ++ (peelCert todo).1).map (·.toWorkItem.bits)) b u
            (residue f x.l (guard + x.p) hf accVal) lossSum,
           ask ctx nd.toWorkItem.bits 0, countWord (F nd.toWorkItem.bits).n) := by
        refine ⟨nd, cert, 0, nd :: todoNodes tail, done ++ (peelCert todo).1,
          true, b, u, lossSum, accVal, cert.hd, Nat.zero_le _, hb, hu, by omega,
          htot_len, hpend_d, hdone'_d, rfl, hask0, ?_⟩
        rw [hn_eq, hask0]; exact cert.hrun0
      split_ifs at he with hwb hd_lt
      · rcases List.mem_cons.mp he with rfl | he1
        · exact hcnt_cov
        · let dFin : Fin cert.nBranches := ⟨u % 2 ^ D4RankWalker.digitWidth (F nd.toWorkItem.bits).n, hn_eq ▸ hd_lt⟩
          let dOrig : Fin (F nd.toWorkItem.bits).n := ⟨u % 2 ^ D4RankWalker.digitWidth (F nd.toWorkItem.bits).n, hd_lt⟩
          let ν := cert.order dFin
          have hask_d := active_ask_eq guard cert (dFin.val + 1)
          have hrund := cert.hrun_br dFin
          dsimp only at hrund
          rw [← hask_d] at hrund
          have hbr : (F nd.toWorkItem.bits).branch dOrig = cert.s.bits hf ν :=
            soloStepFn_branch_eq hrun0 dOrig hrund
          rcases List.mem_cons.mp he1 with rfl | he2
          · refine ⟨nd, cert, dFin.val + 1, nd :: todoNodes tail, done ++ (peelCert todo).1,
              false, b - D4RankWalker.digitWidth (F nd.toWorkItem.bits).n,
              u / 2 ^ D4RankWalker.digitWidth (F nd.toWorkItem.bits).n, lossSum, accVal,
              cert.hd, dFin.isLt, by omega,
              (Nat.div_le_self _ _).trans_lt hu, by omega,
              htot_len, hpend_d, hdone'_d, rfl, hask_d, ?_⟩
            change RunsWithin M_node o_node _ ((F nd.toWorkItem.bits).branch dOrig) _ _
            rw [hbr, hask_d]; exact cert.hrun_br dFin
          · change e ∈ callsV2 ctx F fuel
              (children nd.toWorkItem.bits ((F nd.toWorkItem.bits).branch dOrig) ++
                (todoNodes tail).map (·.toWorkItem.bits))
              ((done ++ (peelCert todo).1).map (·.toWorkItem.bits))
              (b - D4RankWalker.digitWidth (F nd.toWorkItem.bits).n)
              (u / 2 ^ D4RankWalker.digitWidth (F nd.toWorkItem.bits).n)
              (productV2 ctx (residue f x.l (guard + x.p) hf accVal) ((F nd.toWorkItem.bits).branch dOrig))
              (lossSum + stepLoss ctx nd.toWorkItem.bits) at he2
            rw [hbr] at he2
            have hch_eq : children nd.toWorkItem.bits (cert.s.bits hf ν) =
                List.ofFn (fun g : Fin 64 => (cert.childNode ν g).toWorkItem.bits) :=
              (childSoloNode_children_eq x hf E_pkt o_pkt K_loc nd cert.s rfl cert.hbal cert.hM_le
                cert.hinc_le cert.hpkt_eval cert.hdeg_f cert.hu_pos cert.hu_le_M ν).symm
            let loss₀ := AppendixD4.loss nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) 0
            let w_val : B f x.l (guard + x.p) :=
              lift hf (guard + x.p) (AdjoinRoot.of _ (cert.s.weight ν.1 ν.2.1) : B f x.l (nd.pCurr + loss₀))
            have hp_le : nd.pCurr + loss₀ ≤ guard + x.p := active_hp_le_guard cert
            have hans_fld : fld (cert.s.bits hf ν) 1 = residue f x.l (guard + x.p) hf w_val := by
              have hfld1 : fld (cert.s.bits hf ν) 1 =
                  residue f x.l (nd.pCurr + loss₀) hf (AdjoinRoot.of _ (cert.s.weight ν.1 ν.2.1)) := by
                unfold Step.bits; simp [loss₀]
              rw [hfld1]; exact residue_eq_residue_lift hf x.l hp_le _
            have hprod : productV2 ctx (residue f x.l (guard + x.p) hf accVal) (cert.s.bits hf ν) =
                residue f x.l (guard + x.p) hf (accVal * w_val) :=
              productV2_eq_residue_mul x.S x.m x.p guard x.l f hf hRing x.hl
                (Nat.add_pos_right _ x.hp) _ _ accVal w_val rfl hans_fld
            have hsloss : stepLoss ctx nd.toWorkItem.bits = loss₀ := stepLoss_ctx_eq guard nd cert.hd
            let chList : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :=
              List.ofFn fun g : Fin 64 => ⟨k, cert.childNode ν g, sub ν g⟩
            have htodo_next : ((todoNodes (chList ++ tail)).map (·.toWorkItem.bits)) =
                children nd.toWorkItem.bits (cert.s.bits hf ν) ++ (todoNodes tail).map (·.toWorkItem.bits) := by
              rw [hch_eq]
              simp only [todoNodes, chList, List.map_append, List.ofFn_eq_map, List.map_map]
              rfl
            rw [← htodo_next, hprod, hsloss] at he2
            have hrs_peel : 1 + 64 * D4GuardTree.slots k + remSlots tail ≤ remSlots todo := by
              have h1 := peelCert_remSlots_le todo
              rw [hrem] at h1
              simpa [remSlots, D4GuardTree.slots, Nat.add_assoc] using h1
            have hrs_next : remSlots (chList ++ tail) = 64 * D4GuardTree.slots k + remSlots tail :=
              active_children_remSlots k cert sub ν tail
            have hrl_peel : (peelCert todo).1.length + (64 ^ (k + 1) + remLeaves tail) ≤ remLeaves todo := by
              have h1 := peelCert_remLeaves_le todo
              rw [hrem] at h1; simpa [remLeaves] using h1
            have hrl_next : remLeaves (chList ++ tail) = 64 ^ (k + 1) + remLeaves tail :=
              active_children_remLeaves k cert sub ν tail
            have hloss₀_le : loss₀ ≤ localAllowance x.S D :=
              loss_le_localAllowance x.S D nd.d nd.G.nE cert.hd.le cert.hM_le cert.hu_pos
            apply ih (chList ++ tail) (done ++ (peelCert todo).1)
              (b - D4RankWalker.digitWidth (F nd.toWorkItem.bits).n)
              (u / 2 ^ D4RankWalker.digitWidth (F nd.toWorkItem.bits).n)
              (accVal * w_val) (lossSum + loss₀)
            · intro it hit
              rcases List.mem_append.mp hit with hch | htl
              · obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hch
                have hd_nd : ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ ∈ todo := by
                  have hmem2 : (⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ : WorkCertItem ..) ∈ (peelCert todo).2 := by
                    rw [hrem]; exact List.mem_cons_self
                  have hsub : ∀ xs : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc),
                      ∀ y ∈ (peelCert xs).2, y ∈ xs := by
                    intro xs; induction xs with
                    | nil => intro _ hy; cases hy
                    | cons z zs ihz =>
                      rcases z with ⟨kz, ndz, uz⟩
                      cases kz with
                      | zero => intro y hy; exact List.mem_cons_of_mem _ (ihz y hy)
                      | succ kz =>
                        cases uz with
                        | inl _ => intro y hy; exact List.mem_cons_of_mem _ (ihz y hy)
                        | inr _ => intro y hy; exact hy
                  exact hsub todo _ hmem2
                have hd0 := hdepth _ hd_nd
                change (nd.d + 1) + k = D
                dsimp only at hd0; omega
              · have hsub : ∀ xs : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc),
                    ∀ y ∈ (peelCert xs).2, y ∈ xs := by
                  intro xs; induction xs with
                  | nil => intro _ hy; cases hy
                  | cons z zs ihz =>
                    rcases z with ⟨kz, ndz, uz⟩
                    cases kz with
                    | zero => intro y hy; exact List.mem_cons_of_mem _ (ihz y hy)
                    | succ kz =>
                      cases uz with
                      | inl _ => intro y hy; exact List.mem_cons_of_mem _ (ihz y hy)
                      | inr _ => intro y hy; exact hy
                exact hdepth it (hsub todo it (by rw [hrem]; exact List.mem_cons_of_mem _ htl))
            · exact hdone'_d
            · rw [hrs_next]
              have hmul_le : localAllowance x.S D * (1 + (64 * D4GuardTree.slots k + remSlots tail)) ≤
                  localAllowance x.S D * remSlots todo :=
                Nat.mul_le_mul_left _ (by omega)
              rw [Nat.mul_add, Nat.mul_one] at hmul_le
              omega
            · rw [List.length_append, hrl_next]; omega
            · omega
            · exact (Nat.div_le_self _ _).trans_lt hu
            · exact he2
      · simp only [List.mem_singleton] at he; subst he; exact hcnt_cov
      · simp only [List.mem_singleton] at he; subst he; exact hcnt_cov

end SyncTheorems

end

end DetDLP.D4SoloSync

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ),
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let F := soloStepFn M_node o_node ctx
    (RingOK f →
      ∀ (fuel : ℕ)
        (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
        (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
        (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
        remSlots todo ≤ fuel →
        treeMap (SoloLeafData.toBits ctx)
          (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum) =
        unrollAuxV2 ctx F fuel ((todoNodes todo).map (·.toWorkItem.bits))
          (done.map (·.toWorkItem.bits)) (residue f x.l (guard + x.p) hf accVal) lossSum) ∧
    (∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      remSlots todo ≤ fuel →
      lossSum + localAllowance x.S D * remSlots todo ≤ guard →
      done.length + remLeaves todo ≤ 64 ^ D →
      (∀ m ∈ done, D ≤ m.d ∨ m.G.nE ≤ D3Stopped.threshold x.S) →
      List.Perm (pinFirsts (done ++ todoNodes todo)) (List.finRange (4 * x.m * x.k)) →
      treeAll SoloLeafData.Valid
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum)) ∧
    (∀ (g_arg fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (g_arg + x.p)) (lossSum : ℕ),
      remSlots todo ≤ fuel →
      D4UnrollBudget.Work x.S D (8 * K_loc)
        ((todoNodes todo).map fun nd => (nd.d, nd.G.nE))
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc g_arg fuel todo done accVal lossSum)) ∧
    (RingOK f →
      ∀ (bBudget fuel : ℕ)
        (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
        (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
        (b u : ℕ) (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
        (∀ it ∈ todo, it.2.1.d + it.1 = D) →
        (∀ m ∈ done, m.d ≤ D) →
        lossSum + localAllowance x.S D * remSlots todo ≤ guard →
        done.length + remLeaves todo ≤ 64 ^ D →
        b ≤ bBudget →
        u < 2 ^ bBudget →
        ∀ e ∈ callsV2 ctx F fuel ((todoNodes todo).map (·.toWorkItem.bits))
          (done.map (·.toWorkItem.bits)) b u (residue f x.l (guard + x.p) hf accVal) lossSum,
        CallCovered x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard bBudget e) := by
  intro C c x f hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
  exact ⟨fun hRing => DetDLP.D4SoloSync.unrollCertFuel_bits_eq x hf hRing M_node E_pkt o_node o_pkt K_loc H_loc c_loc,
    DetDLP.D4SoloSync.unrollCertFuel_all_valid x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc,
    fun g_arg => DetDLP.D4SoloSync.unrollCertFuel_work x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc g_arg,
    fun hRing bBudget => DetDLP.D4SoloSync.unrollCertFuel_calls x hf hRing M_node E_pkt o_node o_pkt K_loc H_loc c_loc bBudget⟩
