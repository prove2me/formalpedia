-- Prove2me | solution 1 for DetDLP.m14_enum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T07:34:38.333169+00:00
-- url     : https://prove2.me/submissions/abd81834-2303-4241-85ca-fa320e0a9005

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
import Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds
import Theorems.Thm_DetDLP_d4_padded_tree_rank_walker_v2_machine
import Theorems.Thm_DetDLP_m14_base_fuel
import Theorems.Thm_DetDLP_m14_plan_obligations
import Theorems.Thm_DetDLP_m14_bounds

set_option autoImplicit false
set_option maxHeartbeats 600000

open Groundwork Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.M14EnumBoundsInternal

noncomputable section

section PolyBoundCombinators

theorem polyBound_mono_K {K₁ K₂ : ℕ} (hK : K₁ ≤ K₂) (n : ℕ) :
    polyBound K₁ n ≤ polyBound K₂ n := by
  unfold polyBound
  exact mul_le_mul (Nat.cast_le.mpr hK)
    (pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) hK)
    (by positivity) (by positivity)

theorem polyBound_mono_n (K : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    polyBound K n₁ ≤ polyBound K n₂ := by
  unfold polyBound
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (add_le_add (Nat.cast_le.mpr hn) le_rfl) K)
    (Nat.cast_nonneg _)

theorem polyBound_const_le (c n : ℕ) : (c : ℝ) ≤ polyBound c n := by
  unfold polyBound
  exact le_mul_of_one_le_right (Nat.cast_nonneg c)
    (one_le_pow₀ (by exact_mod_cast Nat.succ_pos n))

theorem polyBound_add_le (K₁ K₂ n : ℕ) :
    polyBound K₁ n + polyBound K₂ n ≤ polyBound (K₁ + K₂) n := by
  have hp1 : polyBound K₁ n ≤ (K₁ : ℝ) * ((n : ℝ) + 1) ^ (K₁ + K₂) :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (Nat.le_add_right K₁ K₂))
      (Nat.cast_nonneg _)
  have hp2 : polyBound K₂ n ≤ (K₂ : ℝ) * ((n : ℝ) + 1) ^ (K₁ + K₂) :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (Nat.le_add_left K₂ K₁))
      (Nat.cast_nonneg _)
  unfold polyBound
  unfold polyBound at hp1 hp2
  push_cast
  linarith [hp1, hp2]

theorem polyBound_mul_le (K₁ K₂ n : ℕ) :
    polyBound K₁ n * polyBound K₂ n ≤ polyBound (K₁ * K₂ + K₁ + K₂) n := by
  unfold polyBound
  have hcoef : ((K₁ * K₂ : ℕ) : ℝ) ≤ ((K₁ * K₂ + K₁ + K₂ : ℕ) : ℝ) :=
    Nat.cast_le.mpr ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hexp : K₁ + K₂ ≤ K₁ * K₂ + K₁ + K₂ := by
    rw [Nat.add_assoc]; exact Nat.le_add_left _ _
  calc (K₁ : ℝ) * ((n : ℝ) + 1) ^ K₁ * ((K₂ : ℝ) * ((n : ℝ) + 1) ^ K₂)
      = ((K₁ * K₂ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K₁ + K₂) := by
          push_cast; rw [mul_mul_mul_comm, ← pow_add]
    _ ≤ ((K₁ * K₂ + K₁ + K₂ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K₁ * K₂ + K₁ + K₂) :=
        mul_le_mul hcoef
          (pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) hexp)
          (by positivity) (by positivity)

theorem polyBound_comp_le (K₁ K₂ m n : ℕ) (hm : m ≤ K₂ * (n + 1) ^ K₂) :
    polyBound K₁ m ≤ polyBound (compExp K₁ K₂) n := by
  unfold polyBound compExp
  have hm1 : m + 1 ≤ (K₂ + 1) * (n + 1) ^ K₂ := by
    have hp1 : 1 ≤ (n + 1) ^ K₂ := Nat.one_le_pow _ _ (Nat.succ_pos _)
    nlinarith only [hm, hp1]
  have hmr : (m : ℝ) + 1 ≤ ((K₂ + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ K₂ := by
    have hr := (Nat.cast_le (α := ℝ)).mpr hm1
    push_cast at hr ⊢
    exact hr
  have hpow : ((m : ℝ) + 1) ^ K₁ ≤ (((K₂ + 1) ^ K₁ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K₂ * K₁) := by
    calc ((m : ℝ) + 1) ^ K₁
        ≤ (((K₂ + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ K₂) ^ K₁ :=
          pow_le_pow_left₀ (by positivity) hmr K₁
      _ = (((K₂ + 1) ^ K₁ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K₂ * K₁) := by
          rw [mul_pow, ← pow_mul]; push_cast; rfl
  calc (K₁ : ℝ) * ((m : ℝ) + 1) ^ K₁
      ≤ (K₁ : ℝ) * ((((K₂ + 1) ^ K₁ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K₂ * K₁)) :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
    _ = ((K₁ * (K₂ + 1) ^ K₁ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K₂ * K₁) := by
        push_cast; ring
    _ ≤ ((K₁ * (K₂ + 1) ^ K₁ + K₂ * K₁ : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ (K₁ * (K₂ + 1) ^ K₁ + K₂ * K₁) := by
        apply mul_le_mul
        · exact_mod_cast Nat.le_add_right _ _
        · exact pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (Nat.le_add_left _ _)
        · positivity
        · positivity

end PolyBoundCombinators

section PortsBoundedPropagation

private theorem peelCert_portsBounded {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (xs : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
    (hpb : ∀ it ∈ xs, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2) :
    (∀ m ∈ (peelCert xs).1, NodePortsBounded x.S m) ∧
    (∀ it ∈ (peelCert xs).2, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2) := by
  induction xs with
  | nil => exact And.intro (fun _ h => by cases h) (fun _ h => by cases h)
  | cons z zs ih =>
    have hz := hpb z List.mem_cons_self
    have hzs : ∀ it ∈ zs, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2 :=
      fun it hit => hpb it (List.mem_cons_of_mem _ hit)
    rcases z with ⟨kz, ndz, uz⟩
    cases kz with
    | zero =>
      refine ⟨fun m hm => ?_, (ih hzs).2⟩
      rcases List.mem_cons.mp hm with rfl | hrest
      · exact hz
      · exact (ih hzs).1 m hrest
    | succ kz =>
      cases uz with
      | inl _ =>
        refine ⟨fun m hm => ?_, (ih hzs).2⟩
        rcases List.mem_cons.mp hm with rfl | hrest
        · exact hz
        · exact (ih hzs).1 m hrest
      | inr _ =>
        exact And.intro (fun _ h => by cases h) hpb

theorem unrollCertFuel_done_portsBounded {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc guard : ℕ) :
    ∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      (∀ it ∈ todo, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2) →
      (∀ m ∈ done, NodePortsBounded x.S m) →
      treeAll (fun lf => ∀ m ∈ lf.doneNodes, NodePortsBounded x.S m)
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum) := by
  intro fuel
  induction fuel with
  | zero =>
    intro todo done accVal lossSum htodo hdone
    simp only [unrollCertFuel, treeAll]
    intro m hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact hdone m h1
    · exact (peelCert_portsBounded todo htodo).1 m h2
  | succ fuel ih =>
    intro todo done accVal lossSum htodo hdone
    have hp := peelCert_portsBounded todo htodo
    have hdone' : ∀ m ∈ done ++ (peelCert todo).1, NodePortsBounded x.S m := by
      intro m hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact hdone m h1
      · exact hp.1 m h2
    rcases peelCert_rem_shape todo with hrem0 | ⟨k, nd, cert, sub, tail, hrem⟩
    · simp only [unrollCertFuel, hrem0, treeAll]
      exact hdone'
    · simp only [unrollCertFuel, hrem, treeAll]
      intro d
      apply ih
      · intro it hit
        rcases List.mem_append.mp hit with hch | htl
        · obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hch
          have hhead := hp.2 ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ (by rw [hrem]; exact List.mem_cons_self)
          exact hhead.2 (cert.order d) g
        · exact hp.2 it (by rw [hrem]; exact List.mem_cons_of_mem _ htl)
      · exact hdone'

private theorem todoNodes_portsBounded {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    (xs : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
    (hpb : ∀ it ∈ xs, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2) :
    ∀ m ∈ todoNodes xs, NodePortsBounded x.S m := by
  intro m hm
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hm
  have h := hpb it hit
  rcases it with ⟨kz, ndz, uz⟩
  cases kz with
  | zero => exact h
  | succ kz =>
    cases uz with
    | inl _ => exact h
    | inr _ => exact h.1

private theorem active_ask_eq_loc {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
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
    · intro idx _ _
      simp [SoloNode.toWorkItem, SoloNode.host]
  unfold D4NodeQuery.request D2.input
  dsimp only [SoloNode.toWorkItem] at hlist ⊢
  rw [hlist]

theorem callsV2_workItems_bounded {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (hRing : RingOK f)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc W_max : ℕ)
    (hW : ∀ nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf),
      nd.d ≤ Nat.clog 32 (4 * x.m) → NodePortsBounded x.S nd → nd.toWorkItem.bits.length ≤ W_max) :
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let F := soloStepFn M_node o_node ctx
    ∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (b u : ℕ) (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      (∀ it ∈ todo, it.2.1.d + it.1 = D) →
      (∀ it ∈ todo, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2) →
      (∀ m ∈ done, m.d ≤ D ∧ NodePortsBounded x.S m) →
      ∀ e ∈ callsV2 ctx F fuel ((todoNodes todo).map (·.toWorkItem.bits))
        (done.map (·.toWorkItem.bits)) b u (residue f x.l (guard + x.p) hf accVal) lossSum,
      (∀ w ∈ unpack (fld e.1 2), w.length ≤ W_max) ∧
      (∀ w ∈ unpack (fld e.1 3), w.length ≤ W_max) := by
  intro D guard ctx F fuel
  induction fuel with
  | zero =>
    intro todo done b u accVal lossSum _ _ _ e he
    rw [callsV2.eq_def] at he
    dsimp only at he
    split at he
    · cases (by assumption : 0 = Nat.succ _)
    · cases he
  | succ fuel ih =>
    intro todo done b u accVal lossSum hdepth hpb hdone e he
    obtain ⟨htake, hdrop⟩ := peelCert_bits_split guard todo
    have hp := peelCert_portsBounded todo hpb
    have hsub_peel : ∀ xs : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc),
        (∀ m ∈ (peelCert xs).1, m ∈ todoNodes xs) ∧ (∀ y ∈ (peelCert xs).2, y ∈ xs) := by
      intro xs; induction xs with
      | nil => exact And.intro (fun _ h => by cases h) (fun _ h => by cases h)
      | cons z zs ihz =>
        rcases z with ⟨kz, ndz, uz⟩
        cases kz with
        | zero =>
          exact And.intro
            (fun m hm => by rcases List.mem_cons.mp hm with rfl | hr; exact List.mem_cons_self; exact List.mem_cons_of_mem _ (ihz.1 m hr))
            (fun y hy => List.mem_cons_of_mem _ (ihz.2 y hy))
        | succ kz =>
          cases uz with
          | inl _ =>
            exact And.intro
              (fun m hm => by rcases List.mem_cons.mp hm with rfl | hr; exact List.mem_cons_self; exact List.mem_cons_of_mem _ (ihz.1 m hr))
              (fun y hy => List.mem_cons_of_mem _ (ihz.2 y hy))
          | inr _ => exact And.intro (fun _ h => by cases h) (fun _ h => h)
    rcases peelCert_rem_shape todo with hrem0 | ⟨k, nd, cert, sub, tail, hrem⟩
    · rw [callsV2.eq_def] at he
      dsimp only at he
      rw [← hdrop, hrem0] at he
      cases he
    · have hdrop_cons : ((todoNodes todo).map (·.toWorkItem.bits)).drop
          ((((todoNodes todo).map (·.toWorkItem.bits)).map (small ctx)).idxOf false) =
          nd.toWorkItem.bits :: (todoNodes tail).map (·.toWorkItem.bits) := by
        rw [← hdrop, hrem]; rfl
      rw [callsV2.eq_def] at he
      dsimp only at he
      rw [hdrop_cons, ← htake, ← List.map_append] at he
      dsimp only at he
      have hask0 := active_ask_eq_loc guard cert 0
      have hrun0 := cert.hrun0
      dsimp only at hrun0
      rw [← hask0] at hrun0
      have hn_eq : (F nd.toWorkItem.bits).n = cert.nBranches := soloStepFn_n_eq hrun0
      have hhead_pb := hp.2 ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ (by rw [hrem]; exact List.mem_cons_self)
      have htail_pb : ∀ it ∈ tail, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2 :=
        fun it hit => hp.2 it (by rw [hrem]; exact List.mem_cons_of_mem _ hit)
      have hpend_ok : ∀ w ∈ (nd :: todoNodes tail).map (·.toWorkItem.bits), w.length ≤ W_max := by
        intro w hw
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hw
        rcases List.mem_cons.mp hm with rfl | htl
        · exact hW m cert.hd.le hhead_pb.1
        · obtain ⟨it, hit, rfl⟩ := List.mem_map.mp htl
          have hd_it := hdepth it ((hsub_peel todo).2 it (by rw [hrem]; exact List.mem_cons_of_mem _ hit))
          exact hW it.2.1 (by omega) (todoNodes_portsBounded tail htail_pb _ htl)
      have hdone'_ok : ∀ m ∈ done ++ (peelCert todo).1, m.d ≤ D ∧ NodePortsBounded x.S m := by
        intro m hm
        rcases List.mem_append.mp hm with h1 | h2
        · exact hdone m h1
        · obtain ⟨it, hit, rfl⟩ := List.mem_map.mp ((hsub_peel todo).1 m h2)
          exact ⟨by have := hdepth it hit; omega, hp.1 _ h2⟩
      have hdone'_bits : ∀ w ∈ (done ++ (peelCert todo).1).map (·.toWorkItem.bits), w.length ≤ W_max := by
        intro w hw
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hw
        exact hW m (hdone'_ok m hm).1 (hdone'_ok m hm).2
      have hphase : ∀ tagB b' u' acc' loss',
          (∀ w ∈ unpack (fld (phaseStateV2 [tagB] ctx
            (nd.toWorkItem.bits :: (todoNodes tail).map (·.toWorkItem.bits))
            ((done ++ (peelCert todo).1).map (·.toWorkItem.bits)) b' u' acc' loss') 2), w.length ≤ W_max) ∧
          (∀ w ∈ unpack (fld (phaseStateV2 [tagB] ctx
            (nd.toWorkItem.bits :: (todoNodes tail).map (·.toWorkItem.bits))
            ((done ++ (peelCert todo).1).map (·.toWorkItem.bits)) b' u' acc' loss') 3), w.length ≤ W_max) := by
        intro tagB b' u' acc' loss'
        simp only [phaseStateV2, fld_pack, unpack_pack, List.getD_cons_zero, List.getD_cons_succ]
        exact ⟨hpend_ok, hdone'_bits⟩
      split_ifs at he with hwb hd_lt
      · rcases List.mem_cons.mp he with rfl | he1
        · exact hphase true b u _ lossSum
        · rcases List.mem_cons.mp he1 with rfl | he2
          · exact hphase false _ _ _ lossSum
          · let dFin : Fin cert.nBranches := ⟨u % 2 ^ D4RankWalker.digitWidth (F nd.toWorkItem.bits).n, hn_eq ▸ hd_lt⟩
            let dOrig : Fin (F nd.toWorkItem.bits).n := ⟨u % 2 ^ D4RankWalker.digitWidth (F nd.toWorkItem.bits).n, hd_lt⟩
            let ν := cert.order dFin
            have hask_d := active_ask_eq_loc guard cert (dFin.val + 1)
            have hrund := cert.hrun_br dFin
            dsimp only at hrund
            rw [← hask_d] at hrund
            have hbr : (F nd.toWorkItem.bits).branch dOrig = cert.s.bits hf ν :=
              soloStepFn_branch_eq hrun0 dOrig hrund
            change e ∈ callsV2 ctx F fuel
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
            have hp_le : nd.pCurr + loss₀ ≤ guard + x.p := by
              have hp_curr_le : nd.pCurr ≤ x.p + 80 * x.S * 2 ^ D3Stopped.shift x.S nd.d := by
                refine nd.hp_le.trans ?_
                split_ifs with h0
                · exact Nat.le_add_right _ _
                · exact Nat.add_le_add_left (Nat.mul_le_mul_left _
                    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (shift_mono_solo x.S (Nat.sub_le nd.d 1)))) _
              exact step_prec_le_guard x.S D x.p nd.d nd.pCurr nd.G.nE cert.hd cert.hM_le cert.hu_pos hp_curr_le
            have hans_fld : fld (cert.s.bits hf ν) 1 = residue f x.l (guard + x.p) hf w_val := by
              have hfld1 : fld (cert.s.bits hf ν) 1 =
                  residue f x.l (nd.pCurr + loss₀) hf (AdjoinRoot.of _ (cert.s.weight ν.1 ν.2.1)) := by
                unfold Step.bits; simp [loss₀]
              rw [hfld1]
              exact ((DetDLP.d4_residue_lift_eq f x.l _ _ hf hp_le).1 _).symm
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
            apply ih (chList ++ tail) (done ++ (peelCert todo).1) _ _ (accVal * w_val) (lossSum + loss₀)
            · intro it hit
              rcases List.mem_append.mp hit with hch | htl
              · obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hch
                have hd0 := hdepth ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩
                  ((hsub_peel todo).2 _ (by rw [hrem]; exact List.mem_cons_self))
                change (nd.d + 1) + k = D
                dsimp only at hd0; omega
              · exact hdepth it ((hsub_peel todo).2 it (by rw [hrem]; exact List.mem_cons_of_mem _ htl))
            · intro it hit
              rcases List.mem_append.mp hit with hch | htl
              · obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hch
                exact hhead_pb.2 ν g
              · exact htail_pb it htl
            · exact hdone'_ok
            · exact he2
      · simp only [List.mem_singleton] at he; subst he; exact hphase true b u _ lossSum
      · simp only [List.mem_singleton] at he; subst he; exact hphase true b u _ lossSum

end PortsBoundedPropagation

section StandaloneWordLengths

private abbrev countWord_len_le_succ := m14_bounds.1

private abbrev countWord_len_of_le_pow {a m : ℕ} (ha : a ≤ 2 ^ m) :=
  m14_bounds.2.1 ha

private abbrev encodeNatListBin_len_le := m14_bounds.2.2.1

private abbrev pack_len_le := m14_bounds.2.2.2.1

private abbrev graph_encode_len_le := m14_bounds.2.2.2.2.1

theorem width_le_level_solo (S d : ℕ) : D3Stopped.width S d ≤ D3Stopped.level S :=
  (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)

theorem active_nBranches_le_pow2 {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ}
    {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd) :
    cert.nBranches ≤ 2 ^ (24 * (K_loc + 1) * (size x + 1)) := by
  let a := D3Stopped.shift x.S nd.d
  let u := D3Stopped.width x.S nd.d
  let M := nd.G.nE
  let N₁ := size x + 1
  have hS_pos : 1 ≤ x.S := x.hp.trans x.pS
  have hM_N1 : M ≤ N₁ := cert.hM_le.trans ((Nat.le_add_right x.S x.desc.length).trans (Nat.le_succ _))
  have ha_N1 : a ≤ N₁ :=
    (shift_le_level_solo x.S nd.d).trans
      ((m14_base_fuel.2.2.2.2.2.1 x.S).trans ((Nat.le_add_right x.S x.desc.length).trans (Nat.le_succ _)))
  have hcard_eq : cert.nBranches = ∑ t : Node a u, points M a * (cert.s.modes t).count := by
    have h1 : cert.nBranches = Fintype.card (Branch cert.s) :=
      (Fintype.card_fin cert.nBranches).symm.trans (Fintype.card_congr cert.order)
    rw [h1]
    simp only [Branch, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    rfl
  have hmode_nat : ∀ t : Node a u, (cert.s.modes t).count ≤ 2 ^ (16 * K_loc * M) := by
    intro t
    have hdiv_nat := cert.hinc_prec (AppendixD4.level t.val) t.property.2
    have hmul_nat : (nd.pCurr + increase M a u (AppendixD4.level t.val)) * u ≤
        64 * M * tileScale a (AppendixD4.level t.val) :=
      (Nat.mul_le_mul_right u hdiv_nat).trans (Nat.div_mul_le_self _ _)
    have h1_u : (nd.pCurr + increase M a u (AppendixD4.level t.val)) ≤
        64 * M * tileScale a (AppendixD4.level t.val) :=
      (Nat.le_mul_of_pos_right _ cert.hu_pos).trans hmul_nat
    have hts_pos : (0 : ℝ) < (tileScale a (AppendixD4.level t.val) : ℝ) := by
      unfold tileScale; positivity
    have hfrac : (M : ℝ) * (nd.pCurr + increase M a u (AppendixD4.level t.val)) /
        tileScale a (AppendixD4.level t.val) ≤ ((8 * M : ℕ) : ℝ) ^ 2 := by
      rw [div_le_iff₀ hts_pos]
      have hnat_r : ((nd.pCurr : ℝ) + (increase M a u (AppendixD4.level t.val) : ℝ)) ≤
          64 * (M : ℝ) * (tileScale a (AppendixD4.level t.val) : ℝ) := by exact_mod_cast h1_u
      push_cast
      nlinarith [hnat_r, Nat.cast_nonneg (α := ℝ) M]
    have hsqrt : Real.sqrt ((M : ℝ) * (nd.pCurr + increase M a u (AppendixD4.level t.val)) /
        tileScale a (AppendixD4.level t.val)) ≤ ((8 * M : ℕ) : ℝ) :=
      (Real.sqrt_le_sqrt hfrac).trans (Real.sqrt_sq (Nat.cast_nonneg _)).le
    have hexp_le : ((cert.s.modes t).count : ℝ) ≤ Real.exp ((8 * K_loc * M : ℕ) : ℝ) := by
      refine (cert.hmodes t).trans (Real.exp_le_exp.mpr ?_)
      have hm := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg K_loc)
      push_cast at hm ⊢
      linarith [hm]
    have hexp_pow : Real.exp ((8 * K_loc * M : ℕ) : ℝ) ≤ ((2 ^ (16 * K_loc * M) : ℕ) : ℝ) := by
      have he1 : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9.le; linarith
      have hrw : Real.exp ((8 * K_loc * M : ℕ) : ℝ) = (Real.exp 1) ^ (8 * K_loc * M) := by
        rw [← Real.exp_nat_mul, mul_one]
      rw [hrw]
      calc (Real.exp 1) ^ (8 * K_loc * M)
          ≤ (4 : ℝ) ^ (8 * K_loc * M) := pow_le_pow_left₀ (Real.exp_pos 1).le he1 _
        _ = ((2 ^ 2 : ℕ) : ℝ) ^ (8 * K_loc * M) := by norm_num
        _ = ((2 ^ (16 * K_loc * M) : ℕ) : ℝ) := by
            rw [← Nat.cast_pow, ← pow_mul]; congr 2; ring
    exact (Nat.cast_le (α := ℝ)).mp (hexp_le.trans hexp_pow)
  have hpts : points M a ≤ 2 ^ (M + a + 2) := by
    unfold points
    have hM2 : M + 1 ≤ 2 ^ (M + 1) := (Nat.lt_pow_self (by decide : 1 < 2)).le
    calc M * (2 ^ (a + 1) - 1) + 1
        ≤ M * 2 ^ (a + 1) + 1 * 2 ^ (a + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left M (Nat.sub_le _ _))
            (by rw [one_mul]; exact Nat.one_le_pow _ _ (by decide))
      _ = (M + 1) * 2 ^ (a + 1) := by ring
      _ ≤ 2 ^ (M + 1) * 2 ^ (a + 1) := Nat.mul_le_mul_right _ hM2
      _ = 2 ^ (M + a + 2) := by rw [← pow_add]; congr 1; omega
  have hnode_card : Fintype.card (Node a u) ≤ 2 ^ (a + 1) :=
    (Fintype.card_subtype_le _).trans (by simp)
  rw [hcard_eq]
  calc ∑ t : Node a u, points M a * (cert.s.modes t).count
      ≤ ∑ _ : Node a u, 2 ^ (M + a + 2) * 2 ^ (16 * K_loc * M) :=
        Finset.sum_le_sum fun t _ => Nat.mul_le_mul hpts (hmode_nat t)
    _ = Fintype.card (Node a u) * (2 ^ (M + a + 2) * 2 ^ (16 * K_loc * M)) := by
        simp [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ (a + 1) * (2 ^ (M + a + 2) * 2 ^ (16 * K_loc * M)) :=
        Nat.mul_le_mul_right _ hnode_card
    _ = 2 ^ ((a + 1) + (M + a + 2) + 16 * K_loc * M) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ (24 * (K_loc + 1) * N₁) := by
        apply Nat.pow_le_pow_right (by decide)
        have hN1_ge2 : 2 ≤ N₁ := by
          change 2 ≤ x.S + x.desc.length + 1
          omega
        have hKM : K_loc * M ≤ K_loc * N₁ := Nat.mul_le_mul_left K_loc hM_N1
        nlinarith only [hM_N1, ha_N1, hN1_ge2, hKM, Nat.zero_le K_loc]

theorem residue_len_X2 {f : ℤ[X]} {l q C K_grd X : ℕ} (hf : f.Monic) (z : B f l q)
    (hX1 : 1 ≤ X) (hq : q ≤ (K_grd + 1) * X) (hlf : l * f.natDegree ≤ 8 * (C + 1) * X) :
    (residue f l q hf z).length ≤ 64 * (C + 1) * (K_grd + 2) * X ^ 2 := by
  have hr := m14_bounds.2.2.2.2.2.1 f l q hf z
  have h2q : 2 * (q + 1) + 2 ≤ 4 * (K_grd + 2) * X := by nlinarith only [hq, hX1]
  have hmul := Nat.mul_le_mul h2q hlf
  have hpos : 1 ≤ 32 * (C + 1) * (K_grd + 2) * X ^ 2 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.succ_pos _)) (Nat.succ_pos _))
      (by nlinarith only [hX1])
  calc (residue f l q hf z).length
      ≤ (4 * (K_grd + 2) * X) * (8 * (C + 1) * X) + 1 := hr.trans (Nat.add_le_add_right hmul 1)
    _ = 32 * (C + 1) * (K_grd + 2) * X ^ 2 + 1 := by ring
    _ ≤ 32 * (C + 1) * (K_grd + 2) * X ^ 2 + 32 * (C + 1) * (K_grd + 2) * X ^ 2 :=
      Nat.add_le_add_left hpos _
    _ = 64 * (C + 1) * (K_grd + 2) * X ^ 2 := by ring

theorem contextV2_len_X2 (S m p guard l C K_grd X : ℕ) (fBits : Wd)
    (hX1 : 1 ≤ X) (_hS : S ≤ X) (hlev : D3Stopped.level S ≤ X)
    (hD : Nat.clog 32 (4 * m) ≤ 8 * X)
    (h64sh : ∀ d, 64 ^ D3Stopped.shift S d ≤ 64 * X)
    (_hguard : guard ≤ K_grd * X) (_hqp : guard + p ≤ (K_grd + 1) * X)
    (_hl : l ≤ 2 * C * X) (_hfb : fBits.length ≤ 4 * X) :
    (contextV2 S m p guard l fBits).length ≤ 131072 * (C + 2) * (K_grd + 2) * X ^ 2 := by
  have hX_X2 : X ≤ X ^ 2 := by nlinarith only [hX1]
  have hrow_len : ∀ d, (row S d).length ≤ 512 * X := by
    intro d
    unfold row; dsimp only [letFun]
    let cap_r := 64 * X + 2
    have hr1 : (pack [countWord (D3Stopped.shift S d), countWord (D3Stopped.width S d),
        List.replicate (64 ^ D3Stopped.shift S d) true]).length ≤ (2 * cap_r + 2) * 3 + 1 := by
      apply pack_len_le _ cap_r
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact (countWord_len_le_succ _).trans (by have := (shift_le_level_solo S d).trans hlev; dsimp [cap_r]; omega)
      · exact (countWord_len_le_succ _).trans (by have := (width_le_level_solo S d).trans hlev; dsimp [cap_r]; omega)
      · simp only [List.length_replicate]; have := h64sh d; dsimp [cap_r]; omega
    dsimp [cap_r] at hr1; nlinarith only [hr1, hX1]
  have hrows_pack : (pack ((List.range (Nat.clog 32 (4 * m))).map (row S))).length ≤ 8224 * X ^ 2 := by
    have hp1 : (pack ((List.range (Nat.clog 32 (4 * m))).map (row S))).length ≤
        (2 * (512 * X) + 2) * Nat.clog 32 (4 * m) + 1 := by
      refine (pack_len_le _ (512 * X) ?_).trans_eq (by simp)
      intro w hw; obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw; exact hrow_len d
    have hm := Nat.mul_le_mul (le_rfl : 2 * (512 * X) + 2 ≤ 2 * (512 * X) + 2) hD
    nlinarith only [hp1, hm, hX1, hX_X2]
  unfold contextV2; dsimp only [letFun]
  let cap_c := 8224 * X ^ 2 + (K_grd + 1) * X + 2 * C * X + 8 * X + 2
  have hc1 : (pack [countWord (Nat.clog 32 (4 * m)), countWord (D3Stopped.threshold S),
      List.replicate (guard + p) true, List.replicate l true, fBits,
      pack ((List.range (Nat.clog 32 (4 * m))).map (row S)), countWord guard]).length ≤
      (2 * cap_c + 2) * 7 + 1 := by
    apply pack_len_le _ cap_c
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (countWord_len_le_succ _).trans (by dsimp [cap_c]; omega)
    · exact (countWord_len_le_succ _).trans (by
        have hth : D3Stopped.threshold S ≤ 2 * X := by
          unfold D3Stopped.threshold
          exact (Nat.div_le_self _ _).trans (by have := (Nat.sqrt_le_self _).trans hlev; omega)
        dsimp [cap_c]; omega)
    · simp only [List.length_replicate]; dsimp [cap_c]; omega
    · simp only [List.length_replicate]; dsimp [cap_c]; omega
    · dsimp [cap_c]; omega
    · dsimp [cap_c]; omega
    · exact (countWord_len_le_succ guard).trans (by dsimp [cap_c]; omega)
  dsimp [cap_c] at hc1
  have h4X2 : 4 * X ^ 2 ≤ (C + 2) * (K_grd + 2) * X ^ 2 :=
    Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le C, Nat.zero_le K_grd])
  have h2CX2 : 2 * C * X ^ 2 ≤ (C + 2) * (K_grd + 2) * X ^ 2 :=
    Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le C, Nat.zero_le K_grd])
  have h2GX2 : 2 * K_grd * X ^ 2 ≤ (C + 2) * (K_grd + 2) * X ^ 2 :=
    Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le C, Nat.zero_le K_grd])
  have hCX : C * X ≤ C * X ^ 2 := Nat.mul_le_mul_left C hX_X2
  have hGX : K_grd * X ≤ K_grd * X ^ 2 := Nat.mul_le_mul_left K_grd hX_X2
  nlinarith only [hc1, hX1, hX_X2, h4X2, h2CX2, h2GX2, hCX, hGX]

theorem active_req_and_step_len_X2 (G : AppendixD4.Graph) {b_h : ℕ} (host : Fin b_h → Fin G.nV)
    (a u pCurr l j_q C K_loc X : ℕ) (f : ℤ[X]) (lbl : Label a G)
    (hX1 : 1 ≤ X) (hnE : G.nE ≤ X) (hnV_a : a * G.nV ≤ 25 * X) (hnV_X : G.nV ≤ 25 * X)
    (hG_enc : G.encode.length ≤ 25088 * X) (hbh : b_h ≤ 100 * X)
    (ha : a ≤ X) (hu : u ≤ X) (h64a : 64 ^ a ≤ 64 * X)
    (hpCurr : pCurr ≤ 161 * X) (hl : l ≤ 2 * C * X) (hdeg_f : f.natDegree ≤ 4 * X)
    (hj_cw : (countWord j_q).length ≤ 24 * (K_loc + 1) * X + 1) :
    (D4NodeQuery.request G host a u pCurr l f j_q).length ≤
      4194304 * (C + 2) * (K_loc + 2) * X ^ 2 ∧
    (G.nE + pCurr + f.natDegree + l + 2) + (stepInput G a u pCurr l f lbl).length ≤
      4194304 * (C + 2) * (K_loc + 2) * X ^ 2 := by
  have hX_X2 : X ≤ X ^ 2 := by nlinarith only [hX1]
  have hpf : (polynomialBits f).length ≤ 4 * X := by simp [polynomialBits, hdeg_f]
  have hpar_enc : (encodeNatListBin [a, u, pCurr, l]).length ≤ 2048 * (C + 2) * X := by
    have h1 : (encodeNatListBin [a, u, pCurr, l]).length ≤
        (2 * (161 * X + 2 * C * X + 2) + 2) * 4 + 1 := by
      apply encodeNatListBin_len_le _ (161 * X + 2 * C * X + 2)
      intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      refine (countWord_len_le_succ m).trans ?_
      rcases hm with rfl | rfl | rfl | rfl <;> omega
    nlinarith only [h1, hX1]
  have h4X2 : 4 * X ^ 2 ≤ (C + 2) * (K_loc + 2) * X ^ 2 :=
    Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le C, Nat.zero_le K_loc])
  have h2CX2 : 2 * C * X ^ 2 ≤ (C + 2) * (K_loc + 2) * X ^ 2 :=
    Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le C, Nat.zero_le K_loc])
  have h2LX2 : 2 * K_loc * X ^ 2 ≤ (C + 2) * (K_loc + 2) * X ^ 2 :=
    Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le C, Nat.zero_le K_loc])
  have hCX : C * X ≤ C * X ^ 2 := Nat.mul_le_mul_left C hX_X2
  have hLX : K_loc * X ≤ K_loc * X ^ 2 := Nat.mul_le_mul_left K_loc hX_X2
  constructor
  · have hhost_enc : (encodeNatListBin (List.ofFn fun k_p : Fin b_h => (host k_p).val)).length ≤ 6000 * X ^ 2 := by
      have h1 : (encodeNatListBin (List.ofFn fun k_p : Fin b_h => (host k_p).val)).length ≤
          (2 * (25 * X + 1) + 2) * b_h + 1 := by
        refine (encodeNatListBin_len_le _ (25 * X + 1) ?_).trans_eq (by simp)
        intro m hm; obtain ⟨k_p, rfl⟩ := List.mem_ofFn.mp hm
        have hv_lt : (host k_p).val ≤ 25 * X := (host k_p).isLt.le.trans hnV_X
        exact (countWord_len_le_succ _).trans (by omega)
      have hm := Nat.mul_le_mul (le_rfl : 2 * (25 * X + 1) + 2 ≤ 2 * (25 * X + 1) + 2) hbh
      nlinarith only [h1, hm, hX1, hX_X2]
    let cap_d2 := 25088 * X + 64 * X + 6000 * X ^ 2 + 2
    have hd2_len : (D2.input G a host).length ≤ (2 * cap_d2 + 2) * 4 + 1 := by
      apply pack_len_le _ cap_d2
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · dsimp [cap_d2]; omega
      · exact (countWord_len_le_succ a).trans (by dsimp [cap_d2]; omega)
      · simp only [List.length_replicate]; dsimp [cap_d2]; omega
      · dsimp [cap_d2]; omega
    let cap_req := ((2 * cap_d2 + 2) * 4 + 1) + 2048 * (C + 2) * X + 4 * X + (24 * (K_loc + 1) * X + 1)
    have hreq1 : (D4NodeQuery.request G host a u pCurr l f j_q).length ≤ (2 * cap_req + 2) * 4 + 1 := by
      apply pack_len_le _ cap_req
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> (dsimp [cap_req]; omega)
    dsimp [cap_req, cap_d2] at hreq1
    nlinarith only [hreq1, hX1, hX_X2, h4X2, h2CX2, h2LX2, hCX, hLX]
  · let lblList := (List.finRange a).flatMap fun i_a => List.ofFn fun v_a => (lbl i_a v_a).val
    have hlbl_len : lblList.length ≤ 25 * X := by
      have hl1 : lblList.length = a * G.nV := by simp [lblList, List.length_flatMap]
      omega
    have hlbl_enc : (encodeNatListBin lblList).length ≤ 512 * X := by
      have h1 : (encodeNatListBin lblList).length ≤ (2 * 7 + 2) * lblList.length + 1 := by
        apply encodeNatListBin_len_le _ 7
        intro m hm
        simp only [lblList, List.mem_flatMap, List.mem_finRange, List.mem_ofFn, true_and] at hm
        obtain ⟨i_a, v_a, rfl⟩ := hm
        exact countWord_len_of_le_pow (lbl i_a v_a).isLt.le
      omega
    let cap_si := 25088 * X + 2048 * (C + 2) * X + 4 * X + 512 * X
    have hsi1 : (stepInput G a u pCurr l f lbl).length ≤ (2 * cap_si + 2) * 4 + 1 := by
      apply pack_len_le _ cap_si
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      dsimp only [lblList] at hlbl_enc
      rcases hw with rfl | rfl | rfl | rfl <;> (dsimp [cap_si]; omega)
    dsimp [cap_si] at hsi1
    nlinarith only [hsi1, hnE, hpCurr, hdeg_f, hl, hX1, hX_X2, h4X2, h2CX2, hCX]

theorem phaseStateV2_len_X2 (tagW ctx accW : Wd) (pendW doneW : List Wd)
    (b' u' loss' K_wi C_big X : ℕ)
    (hX1 : 1 ≤ X) (hCbig1 : 1 ≤ C_big) (hKW_C : K_wi + 2 ≤ C_big)
    (htag : tagW.length ≤ 1)
    (hctx : ctx.length ≤ 131072 * C_big * X ^ 2)
    (hacc : accW.length ≤ 64 * C_big * X ^ 2)
    (hp_len : pendW.length ≤ 4096 * X) (hp_w : ∀ w ∈ pendW, w.length ≤ K_wi * X)
    (hd_len : doneW.length ≤ 4096 * X) (hd_w : ∀ w ∈ doneW, w.length ≤ K_wi * X)
    (hb_cw : (countWord b').length ≤ 131072 * C_big * X + 1)
    (hu_cw : (countWord u').length ≤ 131072 * C_big * X + 1)
    (hl_cw : (countWord loss').length ≤ C_big * X + 1) :
    (phaseStateV2 tagW ctx pendW doneW b' u' accW loss').length ≤ 8388608 * C_big * X ^ 2 := by
  have hX_X2 : X ≤ X ^ 2 := by nlinarith only [hX1]
  have hp_pack : (pack pendW).length ≤ 16384 * C_big * X ^ 2 := by
    have h1 := pack_len_le pendW (K_wi * X) hp_w
    have hm := Nat.mul_le_mul (le_rfl : 2 * (K_wi * X) + 2 ≤ 2 * (K_wi * X) + 2) hp_len
    have h2 : (2 * (K_wi * X) + 2) * pendW.length + 1 ≤ 16384 * (K_wi + 2) * X ^ 2 := by
      nlinarith only [hm, hX1, hX_X2]
    exact (h1.trans h2).trans (Nat.mul_le_mul_right (X ^ 2) (Nat.mul_le_mul_left 16384 hKW_C))
  have hd_pack : (pack doneW).length ≤ 16384 * C_big * X ^ 2 := by
    have h1 := pack_len_le doneW (K_wi * X) hd_w
    have hm := Nat.mul_le_mul (le_rfl : 2 * (K_wi * X) + 2 ≤ 2 * (K_wi * X) + 2) hd_len
    have h2 : (2 * (K_wi * X) + 2) * doneW.length + 1 ≤ 16384 * (K_wi + 2) * X ^ 2 := by
      nlinarith only [hm, hX1, hX_X2]
    exact (h1.trans h2).trans (Nat.mul_le_mul_right (X ^ 2) (Nat.mul_le_mul_left 16384 hKW_C))
  let cap_st := 131072 * C_big * X ^ 2 + 16384 * C_big * X ^ 2 + 64 * C_big * X ^ 2 +
    131072 * C_big * X + C_big * X + 4
  have hst1 : (phaseStateV2 tagW ctx pendW doneW b' u' accW loss').length ≤ (2 * cap_st + 2) * 8 + 1 := by
    apply pack_len_le _ cap_st
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp [cap_st]; omega)
  dsimp [cap_st] at hst1
  have hCX_2 : C_big * X ≤ C_big * X ^ 2 := Nat.mul_le_mul_left C_big hX_X2
  have h1_c : 1 ≤ C_big * X ^ 2 := Nat.mul_pos hCbig1 (hX1.trans hX_X2)
  nlinarith only [hst1, hCX_2, h1_c]

theorem branch_and_digit_len_X3 :
    ∀ {C c : ℕ} (hC : 0 < C) (x : Input C c) (_hL_level : 1 ≤ D3Stopped.level x.S)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ)
        (_hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
        (_hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
        (hf : (soloPoly x.S).Monic)
        (hdeg_f : (soloPoly x.S).natDegree = 4 * Nat.clog 2 x.S)
        (hpos : 0 < (soloPoly x.S).natDegree),
    let f := soloPoly x.S
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
    let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
    ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc D rootNode),
    let certTree := unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
      [⟨D, rootNode, rootUnroll⟩] [] 1 0
    ∀ (hvalid : treeAll SoloLeafData.Valid certTree)
        (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
        (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
          (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
          HitDegProp x hbLen doneNodes hperm),
    let br := mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all
    ∀ (hverts : ∀ u : Fin (2 ^ B_bud),
          (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).nV ≤
            4 * x.m + 64 ^ Nat.clog 32 (4 * x.m))
        (hdegree : ∀ u : Fin (2 ^ B_bud),
          (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).maxDeg * x.m ≤
            1217 * (C + 1) ^ 3 * x.b)
        (hcorrect :
          answer x = encodeNatListBin (List.ofFn fun j : Fin x.l =>
            word f x.l (guard + x.p) hf
              (∑ u : Fin (2 ^ B_bud), (br u).wVal *
                BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn)
                  (planVOfBr x f guard B_bud br u))
              j ⟨0, hpos⟩ / 2 ^ guard)),
    let P := mkSoloPlanFromBr x f hf hdeg_f hpos guard B_bud br hverts hdegree hcorrect
    ∀ (K_grd K_wi C_big X : ℕ)
        (_hX1 : 1 ≤ X) (_hCbig1 : 1 ≤ C_big)
        (_hC_Cbig : C + 2 ≤ C_big) (_hKG_Cbig : K_grd + 2 ≤ C_big)
        (_hKW_Cbig : K_wi + 2 ≤ C_big) (_hCG_Cbig : (C + 2) * (K_grd + 2) ≤ C_big)
        (_hxS_X : x.S ≤ X) (_hdesc_X : x.desc.length ≤ X) (_hp_X : x.p ≤ X)
        (_hl_X : x.l ≤ 2 * C * X) (_h4m_N1 : 4 * x.m ≤ 2 * (size x + 1)) (_hmk_N1 : 4 * x.m * x.k ≤ 2 * (size x + 1))
        (_hN1_X : size x + 1 ≤ X) (_hN2_X : (size x + 1) ^ 2 ≤ X)
        (_h64D_N2 : 64 ^ Nat.clog 32 (4 * x.m) ≤ 4096 * (size x + 1) ^ 2)
        (_hD_X : Nat.clog 32 (4 * x.m) ≤ 8 * X)
        (_hnV_orig_X : x.G.nV ≤ X) (_hdeg_f_N1 : (soloPoly x.S).natDegree ≤ 4 * (size x + 1))
        (_hq_X : totalGuard x.S (Nat.clog 32 (4 * x.m)) + x.p ≤ (K_grd + 1) * X)
        (_hhdr_X3 : (header P).length ≤
          1048576 * C_big * X ^ 3)
        (_hin_X3 : (D4Plan.input x).length ≤ C_big * X ^ 3)
        (_hnd_tbl_G : ∀ nd : SoloNode x (soloPoly x.S)
            (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) hf),
          nd.d ≤ Nat.clog 32 (4 * x.m) →
          nd.G.encode.length ≤ 25088 * X ∧ nd.pCurr ≤ 161 * X ∧
          nd.toStoppedSpec.tableBits.length ≤ K_wi * X),
        (∀ u : Fin P.N, (branch P u).length ≤ 137438953472 * C_big * X ^ 3) ∧
        (∀ (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u)),
          (digitDesc P u a).length ≤ 2199023255552 * C_big * X ^ 3) := by
  intro C c hC x hL_level M_node E_pkt o_node o_pkt K_loc H_loc c_loc hL_bud hL_grd hf hdeg_f hpos
    f D guard B_bud rootNode rootUnroll certTree hvalid hbLen hdeg_all branches hverts hdegree hcorrect P
    K_grd K_wi C_big X hX1 hCbig1 hC_Cbig hKG_Cbig hKW_Cbig hCG_Cbig
    hxS_X hdesc_X hp_X hl_X h4m_N1 hmk_N1 hN1_X hN2_X h64D_N2 hD_X hnV_orig_X hdeg_f_N1
    hq_X hhdr_X3 hin_X3 hnd_tbl_G
  let N₁ := size x + 1
  have hN1_pos : 1 ≤ N₁ := Nat.succ_pos _
  have hX_X2 : X ≤ X ^ 2 := by nlinarith only [hX1]
  have hX2_X3 : X ^ 2 ≤ X ^ 3 := by
    calc X ^ 2 = X ^ 2 * 1 := (mul_one _).symm
      _ ≤ X ^ 2 * X := Nat.mul_le_mul_left _ hX1
      _ = X ^ 3 := (pow_succ X 2).symm
  have hX_X3 : X ≤ X ^ 3 := hX_X2.trans hX2_X3
  let qPrec := guard + x.p
  let PktOK := pktOKOf E_pkt o_pkt K_loc x f hf
  have hd_tree : treeAll (fun lf => ∀ m ∈ lf.doneNodes, m.d ≤ D) certTree :=
    m14_bounds.2.2.2.2.2.2.2.2.2.2.2.1 x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard
      (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] 1 0
      (fun it hit => by rw [List.mem_singleton] at hit; subst hit; dsimp [rootNode]; rw [rootSoloNode_d]; omega)
      (fun _ hm => by cases hm)
  have hdeg_f_X : f.natDegree ≤ 4 * X := hdeg_f_N1.trans (Nat.mul_le_mul_left 4 hN1_X)
  have hpf_X : (polynomialBits f).length ≤ 4 * X := by
    unfold polynomialBits; simp only [List.length_ofFn]; exact hdeg_f_X
  have hnV_R_all : ∀ u : Fin P.N, (P.R u).nV ≤ 4100 * X := by
    intro u
    have hv := P.vertices u
    have h4mX : 4 * x.m ≤ 2 * X := h4m_N1.trans (Nat.mul_le_mul_left 2 hN1_X)
    have h64X : 64 ^ Nat.clog 32 (4 * x.m) ≤ 4096 * X := h64D_N2.trans (Nat.mul_le_mul_left 4096 hN2_X)
    omega
  have hbr_all : ∀ u : Fin P.N, (branch P u).length ≤ 137438953472 * C_big * X ^ 3 := by
    intro u
    let u' : Fin (2 ^ B_bud) := u
    let L := x.spec.lookupVerts
    let br := branches u'
    have hnV_R := hnV_R_all u
    have hR_X2 : (P.R u).encode.length ≤ 550000000 * X ^ 2 := by
      have hR_enc : (P.R u).encode.length ≤ 32 * (4104 * N₁ ^ 2) ^ 2 := by
        refine (graph_encode_len_le (P.R u)).trans (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left ?_ 2))
        have hv := P.vertices u
        have he := P.edges u
        dsimp only [N₁] at hN1_pos ⊢
        nlinarith only [hv, he, h4m_N1, h64D_N2, hmk_N1, hN1_pos]
      have hN4_X2 : N₁ ^ 4 ≤ X ^ 2 := by
        calc N₁ ^ 4 = (N₁ ^ 2) ^ 2 := by ring
          _ ≤ X ^ 2 := Nat.pow_le_pow_left hN2_X 2
      have h1 : 32 * (4104 * N₁ ^ 2) ^ 2 = 538970112 * N₁ ^ 4 := by ring
      rw [h1] at hR_enc
      exact (hR_enc.trans (Nat.mul_le_mul_left _ hN4_X2)).trans
        (Nat.mul_le_mul_right _ (by norm_num))
    have hsrc_item : ∀ v : Fin (P.R u).nV, (P.source u v).length ≤ 2097152 * C_big * X := by
      have hsrc_gen : ∀ v : Fin (L.card + br.n),
          (Fin.addCases (motive := fun _ => Bits)
            (fun v₀ => lookupDesc x.desc ((getReattachWit x br.n br.leafFn).old v₀).val.val f.natDegree x.l qPrec)
            br.rightSrc v).length ≤ 2097152 * C_big * X := by
        intro v
        by_cases hlt : v.val < L.card
        · let v₀ : Fin L.card := ⟨v.val, hlt⟩
          have hv_eq : v = Fin.castAdd br.n v₀ := rfl
          rw [hv_eq, Fin.addCases_left]
          let j_v := ((getReattachWit x br.n br.leafFn).old v₀).val
          have hj_X : j_v.val ≤ X := j_v.isLt.le.trans hnV_orig_X
          let cap_lk := X + X + 4 * X + 2 * C * X + (K_grd + 1) * X + 2
          have hl1 : (lookupDesc x.desc j_v.val f.natDegree x.l qPrec).length ≤ (2 * cap_lk + 2) * 5 + 2 := by
            unfold lookupDesc
            simp only [List.length_cons]
            refine Nat.add_le_add_right (pack_len_le _ cap_lk ?_) 1
            intro w hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl | rfl | rfl | rfl | rfl
            · dsimp [cap_lk]; omega
            · exact (countWord_len_le_succ _).trans (by dsimp [cap_lk]; omega)
            · exact (countWord_len_le_succ _).trans (by dsimp [cap_lk]; omega)
            · exact (countWord_len_le_succ _).trans (by dsimp [cap_lk]; omega)
            · exact (countWord_len_le_succ _).trans (by dsimp [cap_lk, qPrec, guard, D]; omega)
          dsimp [cap_lk] at hl1
          have hCX : C * X ≤ C_big * X := Nat.mul_le_mul_right X ((Nat.le_add_right C 2).trans hC_Cbig)
          have hGX : K_grd * X ≤ C_big * X := Nat.mul_le_mul_right X ((Nat.le_add_right K_grd 2).trans hKG_Cbig)
          have h1X : X ≤ C_big * X := by simpa only [one_mul] using Nat.mul_le_mul_right X hCbig1
          nlinarith only [hl1, hX1, hCX, hGX, h1X]
        · have hge : L.card ≤ v.val := Nat.le_of_not_lt hlt
          let j : Fin br.n := ⟨v.val - L.card, by have := v.isLt; omega⟩
          have hv_eq : v = Fin.natAdd L.card j := by apply Fin.ext; simp [j, Nat.add_sub_of_le hge]
          rw [hv_eq, Fin.addCases_right]
          let rightGoal (b : PlanBranchData x f PktOK qPrec) : Prop :=
            ∀ j' : Fin b.n, (b.rightSrc j').length ≤ 2097152 * C_big * X
          suffices hrg : rightGoal br from hrg j
          dsimp only [br, branches, rightGoal]
          have hbranch := m14_plan_obligations.2.2.2.2.1 x hf E_pkt o_pkt K_loc guard B_bud
            certTree hvalid hbLen hdeg_all u'
          cases hread : certTree.read B_bud u'.val with
          | none =>
            rw [hbranch.1 hread]
            intro _
            dsimp only
            unfold emptyStoppedDescRaw
            simp only [List.length_cons]
            have hemG : emptyGraphConst.encode.length ≤ 128 := by
              have := graph_encode_len_le emptyGraphConst
              simpa [emptyGraphConst] using this
            have hpk_in : (pack [x.desc, pack []]).length ≤ 4 * X + 10 := by
              have h1 : (pack [x.desc, pack []]).length ≤ (2 * (X + 1) + 2) * 2 + 1 := by
                apply pack_len_le _ (X + 1)
                intro w hw
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
                rcases hw with rfl | rfl
                · omega
                · change 1 ≤ X + 1; omega
              omega
            have hpk_mid : (pack [countWord 0, polynomialBits f, pack [x.desc, pack []]]).length ≤ 128 * X := by
              have h1 : (pack [countWord 0, polynomialBits f, pack [x.desc, pack []]]).length ≤
                  (2 * (8 * X + 10) + 2) * 3 + 1 := by
                apply pack_len_le _ (8 * X + 10)
                intro w hw
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
                rcases hw with rfl | rfl | rfl
                · change 1 ≤ 8 * X + 10; omega
                · omega
                · omega
              omega
            let cap_em := 128 * X + 2 * C * X + 130
            have hem1 : (pack [countWord x.S, countWord x.l, countWord x.p, emptyGraphConst.encode,
                pack [countWord 0, polynomialBits f, pack [x.desc, pack []]]]).length ≤ (2 * cap_em + 2) * 5 + 1 := by
              apply pack_len_le _ cap_em
              intro w hw
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl | rfl | rfl | rfl
              · exact (countWord_len_le_succ x.S).trans (by dsimp [cap_em]; omega)
              · exact (countWord_len_le_succ x.l).trans (by dsimp [cap_em]; omega)
              · exact (countWord_len_le_succ x.p).trans (by dsimp [cap_em]; omega)
              · dsimp [cap_em]; omega
              · dsimp [cap_em]; omega
            dsimp [cap_em] at hem1
            have hCX : C * X ≤ C_big * X := Nat.mul_le_mul_right X ((Nat.le_add_right C 2).trans hC_Cbig)
            have h1X : X ≤ C_big * X := by simpa only [one_mul] using Nat.mul_le_mul_right X hCbig1
            nlinarith only [hem1, hX1, hCX, h1X]
          | some lf =>
            rw [hbranch.2 lf hread]
            intro j'
            dsimp only
            let nd := lf.doneNodes.get j'
            have hnd_d : nd.d ≤ D := treeAll_read hd_tree B_bud u'.val hread nd (List.get_mem _ j')
            obtain ⟨hG_X, hpCurr_X, htbl_X⟩ := hnd_tbl_G nd hnd_d
            unfold stoppedDesc D3Stopped.descOf
            simp only [List.length_cons]
            have hpair : (pack [x.desc, nd.toStoppedSpec.tableBits]).length ≤
                (2 * (X + K_wi * X) + 2) * 2 + 1 := by
              apply pack_len_le _ (X + K_wi * X)
              intro w hw
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl <;> omega
            let cap_do := 8 * X + 4 * X + ((2 * (X + K_wi * X) + 2) * 2 + 1) + 2
            have hdo : (pack [countWord nd.d, polynomialBits f,
                pack [x.desc, nd.toStoppedSpec.tableBits]]).length ≤ (2 * cap_do + 2) * 3 + 1 := by
              apply pack_len_le _ cap_do
              intro w hw
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl | rfl
              · exact (countWord_len_le_succ nd.d).trans (by have : nd.d ≤ 8 * X := hnd_d.trans hD_X; dsimp [cap_do]; omega)
              · dsimp [cap_do]; omega
              · dsimp [cap_do]; omega
            let cap_sd := 25088 * X + 2 * C * X + 161 * X + ((2 * cap_do + 2) * 3 + 1) + 4
            have hsd : (pack [countWord x.S, countWord x.l, countWord nd.pCurr, nd.G.encode,
                pack [countWord nd.d, polynomialBits f,
                  pack [x.desc, nd.toStoppedSpec.tableBits]]]).length ≤ (2 * cap_sd + 2) * 5 + 1 := by
              apply pack_len_le _ cap_sd
              intro w hw
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl | rfl | rfl | rfl
              · exact (countWord_len_le_succ x.S).trans (by dsimp [cap_sd]; omega)
              · exact (countWord_len_le_succ x.l).trans (by dsimp [cap_sd]; omega)
              · exact (countWord_len_le_succ nd.pCurr).trans (by dsimp [cap_sd]; omega)
              · dsimp [cap_sd]; omega
              · dsimp [cap_sd]; omega
            dsimp [cap_sd, cap_do] at hsd
            have hCX : C * X ≤ C_big * X := Nat.mul_le_mul_right X ((Nat.le_add_right C 2).trans hC_Cbig)
            have hWX : K_wi * X ≤ C_big * X := Nat.mul_le_mul_right X ((Nat.le_add_right K_wi 2).trans hKW_Cbig)
            have h1X : X ≤ C_big * X := by simpa only [one_mul] using Nat.mul_le_mul_right X hCbig1
            change (pack [countWord x.S, countWord x.l, countWord nd.pCurr, nd.G.encode,
              pack [countWord nd.d, polynomialBits f, pack [x.desc, nd.toStoppedSpec.tableBits]]]).length + 1 ≤
              2097152 * C_big * X
            nlinarith only [hsd, hX1, hCX, hWX, h1X]
      exact hsrc_gen
    have hsrc_pack : (pack (List.ofFn (P.source u))).length ≤ 17200000000 * C_big * X ^ 2 := by
      have hp1 : (pack (List.ofFn (P.source u))).length ≤
          (2 * (2097152 * C_big * X) + 2) * (P.R u).nV + 1 := by
        refine (pack_len_le _ (2097152 * C_big * X) ?_).trans_eq (by simp)
        intro w hw; obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hw; exact hsrc_item v
      have hm := Nat.mul_le_mul (le_rfl : 2 * (2097152 * C_big * X) + 2 ≤ 2 * (2097152 * C_big * X) + 2) hnV_R
      have h1X2 : X ^ 2 ≤ C_big * X ^ 2 := by simpa only [one_mul] using Nat.mul_le_mul_right (X ^ 2) hCbig1
      have h1_X2 : 1 ≤ X ^ 2 := hX1.trans hX_X2
      nlinarith only [hp1, hm, h1X2, h1_X2, hX_X2]
    have hlf_X : x.l * f.natDegree ≤ 8 * (C + 1) * X := by
      have hl_N1 : x.l ≤ 2 * C * N₁ := by
        have ⟨_, _, _, _, _, hl_x, _, hS_sz, _⟩ := m14_bounds.2.2.2.2.2.2.2.2.1 x
        exact hl_x.trans (Nat.mul_le_mul_left _ (hS_sz.trans (Nat.le_succ _)))
      calc x.l * f.natDegree ≤ (2 * C * N₁) * (4 * N₁) := Nat.mul_le_mul hl_N1 hdeg_f_N1
        _ = 8 * C * N₁ ^ 2 := by ring
        _ ≤ 8 * (C + 1) * X := Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.le_succ C)) hN2_X
    have hres_br : (residue P.f x.l (P.guard + x.p) P.hf (P.w u)).length ≤ 64 * C_big * X ^ 2 := by
      have hr1 := residue_len_X2 hf (P.w u) hX1 hq_X hlf_X
      have hcg : (C + 1) * (K_grd + 2) ≤ C_big :=
        (Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.le_succ C))).trans hCG_Cbig
      calc (residue f x.l qPrec hf (P.w u)).length
          ≤ 64 * (C + 1) * (K_grd + 2) * X ^ 2 := hr1
        _ = 64 * ((C + 1) * (K_grd + 2)) * X ^ 2 := by ring
        _ ≤ 64 * C_big * X ^ 2 := Nat.mul_le_mul_right (X ^ 2) (Nat.mul_le_mul_left 64 hcg)
    let cap_br := 17200000000 * C_big * X ^ 2 + 550000000 * X ^ 2 + 64 * C_big * X ^ 2
    have hbr1 : (branch P u).length ≤ (2 * cap_br + 2) * 3 + 1 := by
      apply pack_len_le _ cap_br
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · dsimp [cap_br]; omega
      · dsimp [cap_br]; omega
      · change (pack (List.ofFn (P.source u))).length ≤ cap_br
        dsimp [cap_br]; omega
    dsimp [cap_br] at hbr1
    have hX2_3 : C_big * X ^ 2 ≤ C_big * X ^ 3 := Nat.mul_le_mul_left C_big hX2_X3
    have h1X3 : X ^ 2 ≤ C_big * X ^ 3 := hX2_X3.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (X ^ 3) hCbig1)
    have h1_c : 1 ≤ C_big * X ^ 3 := Nat.mul_pos hCbig1 (hX1.trans hX_X3)
    nlinarith only [hbr1, hX2_3, h1X3, h1_c]
  refine ⟨hbr_all, fun u a => ?_⟩
  have hnV_R := hnV_R_all u
  have ha_enc : (encodeNatListBin (List.ofFn fun v => (a v).val)).length ≤ 32768 * C_big * X ^ 2 := by
    have h1 : (encodeNatListBin (List.ofFn fun v => (a v).val)).length ≤
        (2 * ((K_grd + 1) * X + 2) + 2) * (P.R u).nV + 1 := by
      refine (encodeNatListBin_len_le _ ((K_grd + 1) * X + 2) ?_).trans_eq (by simp)
      intro m hm
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hm
      have hlt : (a v).val < J P u := (a v).isLt
      have hJ_le : J P u ≤ qPrec + 1 := by
        change digits qPrec (h P u) ≤ qPrec + 1
        unfold digits; exact Nat.add_le_add_right (Nat.div_le_self _ _) 1
      dsimp only [qPrec, guard, D] at hJ_le
      exact (countWord_len_le_succ _).trans (by omega)
    have hm := Nat.mul_le_mul (le_rfl : 2 * ((K_grd + 1) * X + 2) + 2 ≤ 2 * ((K_grd + 1) * X + 2) + 2) hnV_R
    have hGX2 : (K_grd + 2) * X ^ 2 ≤ C_big * X ^ 2 := Nat.mul_le_mul_right (X ^ 2) hKG_Cbig
    have h1X2 : X ^ 2 ≤ C_big * X ^ 2 := by simpa only [one_mul] using Nat.mul_le_mul_right (X ^ 2) hCbig1
    have h1_X2 : 1 ≤ X ^ 2 := hX1.trans hX_X2
    nlinarith only [h1, hm, hGX2, h1X2, h1_X2, hX_X2]
  have hbr_u := hbr_all u
  let cap_dd := 137438953472 * C_big * X ^ 3 + 1048576 * C_big * X ^ 3 + 32768 * C_big * X ^ 2 + C_big * X ^ 3
  have hdd1 : (digitDesc P u a).length ≤ (2 * cap_dd + 2) * 4 + 1 := by
    apply pack_len_le _ cap_dd
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · dsimp [cap_dd]; omega
    · dsimp [cap_dd]; omega
    · dsimp [cap_dd]; omega
    · dsimp [cap_dd]; omega
  dsimp [cap_dd] at hdd1
  have hX2_3 : C_big * X ^ 2 ≤ C_big * X ^ 3 := Nat.mul_le_mul_left C_big hX2_X3
  have h1_c : 1 ≤ C_big * X ^ 3 := Nat.mul_pos hCbig1 (hX1.trans hX_X3)
  nlinarith only [hdd1, hX2_3, h1_c]

end StandaloneWordLengths

end

end DetDLP.M14EnumBoundsInternal

-- Preserve the hypothesis names in the published statement.
set_option linter.unusedVariables false in
open DetDLP.M14EnumBoundsInternal in
theorem solution :
    (∀ {K₁ K₂ : ℕ} (hK : K₁ ≤ K₂) (n : ℕ),
        polyBound K₁ n ≤ polyBound K₂ n) ∧
    (∀ (K : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂),
        polyBound K n₁ ≤ polyBound K n₂) ∧
    (∀ (c n : ℕ),
        (c : ℝ) ≤ polyBound c n) ∧
    (∀ (K₁ K₂ n : ℕ),
        polyBound K₁ n + polyBound K₂ n ≤ polyBound (K₁ + K₂) n) ∧
    (∀ (K₁ K₂ n : ℕ),
        polyBound K₁ n * polyBound K₂ n ≤ polyBound (K₁ * K₂ + K₁ + K₂) n) ∧
    (∀ (K₁ K₂ m n : ℕ) (hm : m ≤ K₂ * (n + 1) ^ K₂),
        polyBound K₁ m ≤ polyBound (compExp K₁ K₂) n) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc guard : ℕ),
        ∀ (fuel : ℕ)
          (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
          (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
          (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
          (∀ it ∈ todo, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2) →
          (∀ m ∈ done, NodePortsBounded x.S m) →
          treeAll (fun lf => ∀ m ∈ lf.doneNodes, NodePortsBounded x.S m)
            (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum)) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
        (hRing : RingOK f)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc W_max : ℕ)
        (hW : ∀ nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf),
          nd.d ≤ Nat.clog 32 (4 * x.m) → NodePortsBounded x.S nd → nd.toWorkItem.bits.length ≤ W_max),
        let D := Nat.clog 32 (4 * x.m)
        let guard := totalGuard x.S D
        let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
        let F := soloStepFn M_node o_node ctx
        ∀ (fuel : ℕ)
          (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
          (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
          (b u : ℕ) (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
          (∀ it ∈ todo, it.2.1.d + it.1 = D) →
          (∀ it ∈ todo, SoloUnrollAllPortsBounded it.1 it.2.1 it.2.2) →
          (∀ m ∈ done, m.d ≤ D ∧ NodePortsBounded x.S m) →
          ∀ e ∈ callsV2 ctx F fuel ((todoNodes todo).map (·.toWorkItem.bits))
            (done.map (·.toWorkItem.bits)) b u (residue f x.l (guard + x.p) hf accVal) lossSum,
          (∀ w ∈ unpack (fld e.1 2), w.length ≤ W_max) ∧
          (∀ w ∈ unpack (fld e.1 3), w.length ≤ W_max)) ∧
    (∀ (S d : ℕ),
        D3Stopped.width S d ≤ D3Stopped.level S) ∧
    (∀ {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
        {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
        {K_loc H_loc c_loc : ℕ}
        {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
        (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd),
        cert.nBranches ≤ 2 ^ (24 * (K_loc + 1) * (size x + 1))) ∧
    (∀ {f : ℤ[X]} {l q C K_grd X : ℕ} (hf : f.Monic) (z : B f l q)
        (hX1 : 1 ≤ X) (hq : q ≤ (K_grd + 1) * X) (hlf : l * f.natDegree ≤ 8 * (C + 1) * X),
        (residue f l q hf z).length ≤ 64 * (C + 1) * (K_grd + 2) * X ^ 2) ∧
    (∀ (S m p guard l C K_grd X : ℕ) (fBits : Wd)
        (hX1 : 1 ≤ X) (_hS : S ≤ X) (hlev : D3Stopped.level S ≤ X)
        (hD : Nat.clog 32 (4 * m) ≤ 8 * X)
        (h64sh : ∀ d, 64 ^ D3Stopped.shift S d ≤ 64 * X)
        (_hguard : guard ≤ K_grd * X) (_hqp : guard + p ≤ (K_grd + 1) * X)
        (_hl : l ≤ 2 * C * X) (_hfb : fBits.length ≤ 4 * X),
        (contextV2 S m p guard l fBits).length ≤ 131072 * (C + 2) * (K_grd + 2) * X ^ 2) ∧
    (∀ (G : AppendixD4.Graph) {b_h : ℕ} (host : Fin b_h → Fin G.nV)
        (a u pCurr l j_q C K_loc X : ℕ) (f : ℤ[X]) (lbl : Label a G)
        (hX1 : 1 ≤ X) (hnE : G.nE ≤ X) (hnV_a : a * G.nV ≤ 25 * X) (hnV_X : G.nV ≤ 25 * X)
        (hG_enc : G.encode.length ≤ 25088 * X) (hbh : b_h ≤ 100 * X)
        (ha : a ≤ X) (hu : u ≤ X) (h64a : 64 ^ a ≤ 64 * X)
        (hpCurr : pCurr ≤ 161 * X) (hl : l ≤ 2 * C * X) (hdeg_f : f.natDegree ≤ 4 * X)
        (hj_cw : (countWord j_q).length ≤ 24 * (K_loc + 1) * X + 1),
        (D4NodeQuery.request G host a u pCurr l f j_q).length ≤
          4194304 * (C + 2) * (K_loc + 2) * X ^ 2 ∧
        (G.nE + pCurr + f.natDegree + l + 2) + (stepInput G a u pCurr l f lbl).length ≤
          4194304 * (C + 2) * (K_loc + 2) * X ^ 2) ∧
    (∀ (tagW ctx accW : Wd) (pendW doneW : List Wd)
        (b' u' loss' K_wi C_big X : ℕ)
        (hX1 : 1 ≤ X) (hCbig1 : 1 ≤ C_big) (hKW_C : K_wi + 2 ≤ C_big)
        (htag : tagW.length ≤ 1)
        (hctx : ctx.length ≤ 131072 * C_big * X ^ 2)
        (hacc : accW.length ≤ 64 * C_big * X ^ 2)
        (hp_len : pendW.length ≤ 4096 * X) (hp_w : ∀ w ∈ pendW, w.length ≤ K_wi * X)
        (hd_len : doneW.length ≤ 4096 * X) (hd_w : ∀ w ∈ doneW, w.length ≤ K_wi * X)
        (hb_cw : (countWord b').length ≤ 131072 * C_big * X + 1)
        (hu_cw : (countWord u').length ≤ 131072 * C_big * X + 1)
        (hl_cw : (countWord loss').length ≤ C_big * X + 1),
        (phaseStateV2 tagW ctx pendW doneW b' u' accW loss').length ≤ 8388608 * C_big * X ^ 2) ∧
    (∀ {C c : ℕ} (hC : 0 < C) (x : Input C c) (hL_level : 1 ≤ D3Stopped.level x.S)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ)
        (hL_bud : (DetDLP.d4_unroll_tree_bit_budget C (8 * K_loc) hC).choose ≤ D3Stopped.level x.S)
        (hL_grd : (DetDLP.d4_unroll_guard_and_residual_bounds C hC).choose ≤ D3Stopped.level x.S)
        (hf : (soloPoly x.S).Monic)
        (hdeg_f : (soloPoly x.S).natDegree = 4 * Nat.clog 2 x.S)
        (hpos : 0 < (soloPoly x.S).natDegree),
    let f := soloPoly x.S
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
    let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
    ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc D rootNode),
    let certTree := unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
      [⟨D, rootNode, rootUnroll⟩] [] 1 0
    ∀ (hvalid : treeAll SoloLeafData.Valid certTree)
        (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
        (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
          (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
          HitDegProp x hbLen doneNodes hperm),
    let br := mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all
    ∀ (hverts : ∀ u : Fin (2 ^ B_bud),
          (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).nV ≤
            4 * x.m + 64 ^ Nat.clog 32 (4 * x.m))
        (hdegree : ∀ u : Fin (2 ^ B_bud),
          (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).maxDeg * x.m ≤
            1217 * (C + 1) ^ 3 * x.b)
        (hcorrect :
          answer x = encodeNatListBin (List.ofFn fun j : Fin x.l =>
            word f x.l (guard + x.p) hf
              (∑ u : Fin (2 ^ B_bud), (br u).wVal *
                BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn)
                  (planVOfBr x f guard B_bud br u))
              j ⟨0, hpos⟩ / 2 ^ guard)),
    let P := mkSoloPlanFromBr x f hf hdeg_f hpos guard B_bud br hverts hdegree hcorrect
    ∀ (K_grd K_wi C_big X : ℕ)
        (hX1 : 1 ≤ X) (hCbig1 : 1 ≤ C_big)
        (hC_Cbig : C + 2 ≤ C_big) (hKG_Cbig : K_grd + 2 ≤ C_big)
        (hKW_Cbig : K_wi + 2 ≤ C_big) (hCG_Cbig : (C + 2) * (K_grd + 2) ≤ C_big)
        (hxS_X : x.S ≤ X) (hdesc_X : x.desc.length ≤ X) (hp_X : x.p ≤ X)
        (hl_X : x.l ≤ 2 * C * X) (h4m_N1 : 4 * x.m ≤ 2 * (size x + 1)) (hmk_N1 : 4 * x.m * x.k ≤ 2 * (size x + 1))
        (hN1_X : size x + 1 ≤ X) (hN2_X : (size x + 1) ^ 2 ≤ X)
        (h64D_N2 : 64 ^ Nat.clog 32 (4 * x.m) ≤ 4096 * (size x + 1) ^ 2)
        (hD_X : Nat.clog 32 (4 * x.m) ≤ 8 * X)
        (hnV_orig_X : x.G.nV ≤ X) (hdeg_f_N1 : (soloPoly x.S).natDegree ≤ 4 * (size x + 1))
        (hq_X : totalGuard x.S (Nat.clog 32 (4 * x.m)) + x.p ≤ (K_grd + 1) * X)
        (hhdr_X3 : (header P).length ≤
          1048576 * C_big * X ^ 3)
        (hin_X3 : (D4Plan.input x).length ≤ C_big * X ^ 3)
        (hnd_tbl_G : ∀ nd : SoloNode x (soloPoly x.S)
            (pktOKOf E_pkt o_pkt K_loc x (soloPoly x.S) hf),
          nd.d ≤ Nat.clog 32 (4 * x.m) →
          nd.G.encode.length ≤ 25088 * X ∧ nd.pCurr ≤ 161 * X ∧
          nd.toStoppedSpec.tableBits.length ≤ K_wi * X),
        (∀ u : Fin P.N, (branch P u).length ≤ 137438953472 * C_big * X ^ 3) ∧
        (∀ (u : Fin P.N) (a : Fin (P.R u).nV → Fin (J P u)),
          (digitDesc P u a).length ≤ 2199023255552 * C_big * X ^ 3)) :=
  ⟨@polyBound_mono_K, @polyBound_mono_n, polyBound_const_le, polyBound_add_le,
   polyBound_mul_le, polyBound_comp_le, @unrollCertFuel_done_portsBounded,
   @callsV2_workItems_bounded, width_le_level_solo, @active_nBranches_le_pow2,
   @residue_len_X2, contextV2_len_X2, @active_req_and_step_len_X2, phaseStateV2_len_X2,
   @branch_and_digit_len_X3⟩
