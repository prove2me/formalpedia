-- Prove2me | solution 1 for DetDLP.m14_total
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T08:12:05.173892+00:00
-- url     : https://prove2.me/submissions/0c0774b4-2854-4b10-8623-2677ecb254aa

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_d4_raw_weight_cleared_identity

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace DetDLP.M14TotalInternal

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4GuardTree.Expansion DetDLP.D4SoloRaw DetDLP.D4SoloNode
open DetDLP.D4SoloRoot DetDLP.D4SoloStep DetDLP.D4SoloStepEq DetDLP.D4SoloTree
open DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable section

theorem prod_map_ofFn {α β : Type} [CommMonoid β] (n : ℕ) (fn : Fin n → α) (g : α → β) :
    ((List.ofFn fn).map g).prod = ∏ i : Fin n, g (fn i) := by
  rw [Fin.prod_univ_def]
  congr 1
  exact List.ext_getElem (by simp) (fun _ _ _ => by simp)

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
    List.ext_getElem (by simp) (fun _ _ _ => by simp)
  rw [hmap, List.sum_replicate, smul_eq_mul]







theorem expSum_eq_rec {S l d k p : ℕ} {f : ℤ[X]} {hf : f.Monic}
    {z₁ z₂ : B f l p} (h : z₁ = z₂) (q A : ℕ) (e : Expansion S f hf l d k p z₁) :
    expSum q A (Eq.rec (motive := fun z _ => Expansion S f hf l d k p z) e h) = expSum q A e := by
  subst h; rfl

theorem rawLossSum_le_slots {S D l d k p : ℕ} {f : ℤ[X]} {hf : f.Monic} {z : B f l p}
    (e : Expansion S f hf l d k p z) (hdk : d + k ≤ D) :
    ∀ r : e.Ranks, rawLossSum e r ≤ localAllowance S D * D4GuardTree.slots k := by
  induction e with
  | leaf _ => intro _; simp [rawLossSum]
  | @step d₀ k₀ p₀ b₀ G host lbl hu s ok T η₀ hM hw next ih =>
    rintro ⟨ν, r_ch⟩
    simp only [rawLossSum, D4GuardTree.slots]
    have hloss₀ : AppendixD4.loss G.nE (D3Stopped.shift S d₀) (D3Stopped.width S d₀) 0 ≤
        localAllowance S D :=
      loss_le_localAllowance S D d₀ G.nE (by omega) hM hw
    have hsum : ∑ j : Fin 64, rawLossSum (next ν j) (r_ch j) ≤
        64 * (localAllowance S D * D4GuardTree.slots k₀) := by
      calc ∑ j : Fin 64, rawLossSum (next ν j) (r_ch j)
          ≤ ∑ _ : Fin 64, localAllowance S D * D4GuardTree.slots k₀ :=
            Finset.sum_le_sum fun j _ => ih ν j (by omega) (r_ch j)
        _ = 64 * (localAllowance S D * D4GuardTree.slots k₀) := by
            simp [Finset.sum_const]
    calc AppendixD4.loss G.nE (D3Stopped.shift S d₀) (D3Stopped.width S d₀) 0 +
          ∑ j : Fin 64, rawLossSum (next ν j) (r_ch j)
        ≤ localAllowance S D + 64 * (localAllowance S D * D4GuardTree.slots k₀) :=
          Nat.add_le_add hloss₀ hsum
      _ = localAllowance S D * (1 + 64 * D4GuardTree.slots k₀) := by ring

private theorem sub_sum_fin64 (B₀ : ℕ) (xF : Fin 64 → ℕ) (hle : ∀ g, xF g ≤ B₀) :
    64 * B₀ - ∑ g : Fin 64, xF g = ∑ g : Fin 64, (B₀ - xF g) := by
  have hsum_add : (∑ g : Fin 64, (B₀ - xF g)) + ∑ g : Fin 64, xF g = 64 * B₀ := by
    rw [← Finset.sum_add_distrib]
    calc ∑ g : Fin 64, (B₀ - xF g + xF g)
        = ∑ _ : Fin 64, B₀ := Finset.sum_congr rfl fun g _ => Nat.sub_add_cancel (hle g)
      _ = 64 * B₀ := by simp [Finset.sum_const]
  omega

private theorem ring_exp_step {R : Type} [CommRing R] (a b p1 p2 p3 : R) :
    (a * p1) * (b * p2) * p3 = (a * b) * (p1 * p2 * p3) := by ring

theorem pow_add2 {R : Type} [Monoid R] (z : R) {m a b : ℕ} (h : m = a + b) :
    z ^ m = z ^ a * z ^ b := by subst h; rw [pow_add]

theorem pow_add3 {R : Type} [Monoid R] (z : R) {m a b c : ℕ} (h : m = a + b + c) :
    z ^ m = z ^ a * z ^ b * z ^ c := by subst h; rw [pow_add, pow_add]

theorem expSum_step {S D l d₀ k₀ p₀ b₀ : ℕ} {f : ℤ[X]} {hf : f.Monic}
    {G : Graph} {host : Fin b₀ → Fin G.nV}
    {lbl : Label (D3Stopped.shift S d₀) G} {hu : D3Stopped.width S d₀ ≤ D3Stopped.shift S d₀}
    (s : Step lbl hu f l p₀) (ok : s.sound hf) (T : OpenTensor host (B f l p₀)) (η₀ : Fin b₀ → Bool)
    (hM : G.nE ≤ S) (hw : 1 ≤ D3Stopped.width S d₀)
    (next : (ν : Branch s) → (g : Fin 64) →
      let c := s.child ν.1 ν.2.1 ν.2.2 g
      Expansion S f hf l (d₀ + 1) k₀
        (p₀ + increase G.nE (D3Stopped.shift S d₀) (D3Stopped.width S d₀) (AppendixD4.level ν.1.val))
        (BTNContract c.graph (c.tensor (lift hf _) (pin T η₀))))
    (hdk : d₀ + (k₀ + 1) ≤ D) (q : ℕ) :
    let A := localAllowance S D
    let loss₀ := AppendixD4.loss G.nE (D3Stopped.shift S d₀) (D3Stopped.width S d₀) 0
    expSum q A (Expansion.step s ok T η₀ hM hw next) =
      ∑ ν : Branch s, (2 : B f l q) ^ (A - loss₀) *
        lift hf q (AdjoinRoot.of _ (s.weight ν.1 ν.2.1) : B f l (p₀ + loss₀)) *
        ∏ g : Fin 64, expSum q A (next ν g) := by
  intro A loss₀
  unfold expSum
  change (∑ r : (ν : Branch s) × ((g : Fin 64) → (next ν g).Ranks), _) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro ν _
  have hloss₀_le : loss₀ ≤ A := loss_le_localAllowance S D d₀ G.nE (by omega) hM hw
  have hred_w : red f l q (D4GuardTree.repr hf (AdjoinRoot.of _ (s.weight ν.1 ν.2.1) : B f l (p₀ + loss₀))) =
      lift hf q (AdjoinRoot.of _ (s.weight ν.1 ν.2.1) : B f l (p₀ + loss₀)) :=
    red_repr_eq_lift hf q _
  have hterm : ∀ r_ch : (g : Fin 64) → (next ν g).Ranks,
      (2 : B f l q) ^ (A * D4GuardTree.slots (k₀ + 1) -
          rawLossSum (Expansion.step s ok T η₀ hM hw next) ⟨ν, r_ch⟩) *
        red f l q (rawCoeff (Expansion.step s ok T η₀ hM hw next) ⟨ν, r_ch⟩) *
        (Expansion.step s ok T η₀ hM hw next).leaves q ⟨ν, r_ch⟩ =
      ((2 : B f l q) ^ (A - loss₀) *
        lift hf q (AdjoinRoot.of _ (s.weight ν.1 ν.2.1) : B f l (p₀ + loss₀))) *
        ∏ g : Fin 64, ((2 : B f l q) ^ (A * D4GuardTree.slots k₀ - rawLossSum (next ν g) (r_ch g)) *
          red f l q (rawCoeff (next ν g) (r_ch g)) * (next ν g).leaves q (r_ch g)) := by
    intro r_ch
    have hch_le : ∀ g : Fin 64, rawLossSum (next ν g) (r_ch g) ≤ A * D4GuardTree.slots k₀ :=
      fun g => rawLossSum_le_slots (next ν g) (by omega) (r_ch g)
    have hsum_le : ∑ g : Fin 64, rawLossSum (next ν g) (r_ch g) ≤ 64 * (A * D4GuardTree.slots k₀) := by
      calc ∑ g : Fin 64, rawLossSum (next ν g) (r_ch g)
          ≤ ∑ _ : Fin 64, A * D4GuardTree.slots k₀ := Finset.sum_le_sum fun g _ => hch_le g
        _ = 64 * (A * D4GuardTree.slots k₀) := by simp [Finset.sum_const]
    have hexp_eq : A * D4GuardTree.slots (k₀ + 1) -
        (loss₀ + ∑ g : Fin 64, rawLossSum (next ν g) (r_ch g)) =
        (A - loss₀) + ∑ g : Fin 64, (A * D4GuardTree.slots k₀ - rawLossSum (next ν g) (r_ch g)) := by
      have hmul_slots : A * D4GuardTree.slots (k₀ + 1) = A + 64 * (A * D4GuardTree.slots k₀) := by
        rw [D4GuardTree.slots]; ring
      rw [hmul_slots, ← sub_sum_fin64 (A * D4GuardTree.slots k₀) _ hch_le]
      omega
    simp only [rawLossSum, rawCoeff, Expansion.leaves, map_mul, map_prod, hred_w]
    change (2 : B f l q) ^ (A * D4GuardTree.slots (k₀ + 1) -
        (loss₀ + ∑ g : Fin 64, rawLossSum (next ν g) (r_ch g))) *
      (lift hf q (AdjoinRoot.of _ (s.weight ν.1 ν.2.1)) *
        ∏ g : Fin 64, red f l q (rawCoeff (next ν g) (r_ch g))) *
      (∏ g : Fin 64, (next ν g).leaves q (r_ch g)) = _
    rw [hexp_eq, pow_add, ← Finset.prod_pow_eq_pow_sum]
    have hprod3 : (∏ g : Fin 64, (2 : B f l q) ^ (A * D4GuardTree.slots k₀ - rawLossSum (next ν g) (r_ch g))) *
        (∏ g : Fin 64, red f l q (rawCoeff (next ν g) (r_ch g))) *
        (∏ g : Fin 64, (next ν g).leaves q (r_ch g)) =
        ∏ g : Fin 64, ((2 : B f l q) ^ (A * D4GuardTree.slots k₀ - rawLossSum (next ν g) (r_ch g)) *
          red f l q (rawCoeff (next ν g) (r_ch g)) * (next ν g).leaves q (r_ch g)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rw [← hprod3]
    exact ring_exp_step _ _ _ _ _
  rw [Finset.sum_congr rfl fun r_ch _ => hterm r_ch, ← Finset.mul_sum]
  congr 1
  exact (Fintype.prod_sum fun g r_g =>
    (2 : B f l q) ^ (A * D4GuardTree.slots k₀ - rawLossSum (next ν g) r_g) *
      red f l q (rawCoeff (next ν g) r_g) * (next ν g).leaves q r_g).symm








private theorem ring_peel0 {R : Type} [CommRing R] (a p1 p2 p3 : R) :
    a * (p1 * p2 * p3) = p1 * (a * p2) * p3 := by ring

private theorem ring_peel_succ {R : Type} [CommRing R] (p1 a p2 p3 p4 : R) :
    (p1 * a) * (p2 * p3 * p4) = (p1 * p2) * (a * p3) * p4 := by ring

theorem ring_leaf_rearrange {R : Type} [CommRing R] (p1 p2 a d1 d2 : R) :
    (p1 * p2) * a * (d1 * d2) = p1 * a * d1 * (p2 * d2) := by ring

theorem ring_step_rearrange {R : Type} [CommRing R]
    (g1 g2 g3 a w d1 d2 ch tl : R) :
    (g1 * g2 * g3) * (a * w) * (d1 * d2) * (ch * tl) =
      (g1 * g2 * a * d1 * d2 * tl) * (g3 * w * ch) := by ring

theorem ring_step_finish {R : Type} [CommRing R]
    (g1 g2 a d1 d2 tl s : R) :
    (g1 * g2 * a * d1 * d2 * tl) * s =
      g1 * a * d1 * (g2 * d2 * (s * tl)) := by ring

private theorem expSum_leaf {S l d k p : ℕ} {f : ℤ[X]} {hf : f.Monic}
    (z : B f l p) (q A : ℕ) :
    expSum q A (Expansion.leaf z : Expansion S f hf l d k p z) =
      (2 : B f l q) ^ (A * D4GuardTree.slots k) * lift hf q z := by
  unfold expSum
  change ∑ _ : Unit, (2 : B f l q) ^ (A * D4GuardTree.slots k - 0) * red f l q 1 * lift hf q z = _
  rw [Fintype.sum_unique, Nat.sub_zero, map_one, mul_one]

theorem peelCert_prod_eq {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    {M_node E_pkt : PrimitiveMachine} {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount}
    {K_loc H_loc c_loc : ℕ} (hdeg : 0 < f.natDegree) (η : Fin (4 * x.m * x.k) → Bool)
    (q A : ℕ)
    (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) :
    (todo.map (itemExpSum hdeg η q A)).prod =
      (2 : B f x.l q) ^ (A * (remSlots todo - remSlots (peelCert todo).2)) *
        ((peelCert todo).1.map (SoloNode.pinnedVal hf q η)).prod *
        ((peelCert todo).2.map (itemExpSum hdeg η q A)).prod := by
  induction todo with
  | nil => simp [peelCert, remSlots]
  | cons it rest ih =>
    rcases it with ⟨k, nd, u⟩
    cases k with
    | zero =>
      have hleaf : itemExpSum hdeg η q A
          (⟨0, nd, u⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) =
          SoloNode.pinnedVal hf q η nd := by
        unfold itemExpSum SoloUnroll.toExpansion
        rw [expSum_leaf]
        simp [D4GuardTree.slots, SoloNode.pinnedVal]
      have hrs_eq : remSlots ((⟨0, nd, u⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :: rest) =
          remSlots rest := by
        simp [remSlots, D4GuardTree.slots]
      have hpeel1 : (peelCert ((⟨0, nd, u⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :: rest)).1 =
          nd :: (peelCert rest).1 := rfl
      have hpeel2 : (peelCert ((⟨0, nd, u⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :: rest)).2 =
          (peelCert rest).2 := rfl
      rw [hrs_eq, hpeel1, hpeel2]
      simp only [List.map_cons, List.prod_cons, hleaf, ih]
      exact ring_peel0 _ _ _ _
    | succ k =>
      cases u with
      | inl hs_box =>
        have hleaf : itemExpSum hdeg η q A
            (⟨k + 1, nd, PSum.inl hs_box⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) =
            (2 : B f x.l q) ^ (A * D4GuardTree.slots (k + 1)) * SoloNode.pinnedVal hf q η nd := by
          unfold itemExpSum SoloUnroll.toExpansion
          exact expSum_leaf _ q A
        have hrs_le := peelCert_remSlots_le rest
        have hrs_cons : remSlots ((⟨k + 1, nd, PSum.inl hs_box⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :: rest) =
            D4GuardTree.slots (k + 1) + remSlots rest := by
          simp [remSlots]
        have hpeel1 : (peelCert ((⟨k + 1, nd, PSum.inl hs_box⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :: rest)).1 =
            nd :: (peelCert rest).1 := rfl
        have hpeel2 : (peelCert ((⟨k + 1, nd, PSum.inl hs_box⟩ : WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :: rest)).2 =
            (peelCert rest).2 := rfl
        rw [hrs_cons, hpeel1, hpeel2]
        have hsub_eq : A * (D4GuardTree.slots (k + 1) + remSlots rest - remSlots (peelCert rest).2) =
            A * D4GuardTree.slots (k + 1) + A * (remSlots rest - remSlots (peelCert rest).2) := by
          rw [← Nat.mul_add]; congr 1; omega
        simp only [List.map_cons, List.prod_cons, hleaf, ih, hsub_eq, pow_add]
        exact ring_peel_succ _ _ _ _ _
      | inr _ =>
        simp [peelCert]

private theorem itemExpSum_step {C c : ℕ} {x : Input C c} {f : ℤ[X]} {hf : f.Monic}
    (hdeg : 0 < f.natDegree) {M_node E_pkt : PrimitiveMachine}
    {o_node : Fin M_node.tapeCount} {o_pkt : Fin E_pkt.tapeCount} {K_loc H_loc c_loc : ℕ}
    (k : ℕ) {nd : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)}
    (cert : ActiveNodeCert x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc nd)
    (sub : (ν : Branch cert.s) → (g : Fin 64) →
      SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc k (cert.childNode ν g))
    (hd_nd : nd.d + (k + 1) ≤ Nat.clog 32 (4 * x.m))
    (η : Fin (4 * x.m * x.k) → Bool) (q : ℕ) :
    let D := Nat.clog 32 (4 * x.m)
    let A := localAllowance x.S D
    let loss₀ := AppendixD4.loss nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) 0
    ∑ d : Fin cert.nBranches,
      ((2 : B f x.l q) ^ (A - loss₀) *
        lift hf q (AdjoinRoot.of _ (cert.s.weight (cert.order d).1 (cert.order d).2.1) :
          B f x.l (nd.pCurr + loss₀)) *
        ∏ g : Fin 64, itemExpSum hdeg η q A ⟨k, cert.childNode (cert.order d) g, sub (cert.order d) g⟩) =
      itemExpSum hdeg η q A ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ := by
  intro D A loss₀
  refine (Equiv.sum_comp cert.order (fun ν =>
    (2 : B f x.l q) ^ (A - loss₀) *
      lift hf q (AdjoinRoot.of _ (cert.s.weight ν.1 ν.2.1) : B f x.l (nd.pCurr + loss₀)) *
      ∏ g : Fin 64, itemExpSum hdeg η q A ⟨k, cert.childNode ν g, sub ν g⟩)).trans ?_
  unfold itemExpSum
  dsimp only [SoloUnroll.toExpansion]
  rw [expSum_step cert.s cert.hsound (nd.openTensor hf) (fun j => η (nd.pins.get j).1)
    cert.hM_le cert.hu_pos _ hd_nd q]
  refine Finset.sum_congr rfl fun ν _ => ?_
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun g _ => ?_)
  exact (expSum_eq_rec _ q A (SoloUnroll.toExpansion hdeg η k (cert.childNode ν g) (sub ν g))).symm

theorem unrollCertFuel_total_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc guard : ℕ) (η : Fin (4 * x.m * x.k) → Bool) :
    let D := Nat.clog 32 (4 * x.m)
    let A := localAllowance x.S D
    ∀ (fuel : ℕ)
      (todo : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc))
      (done : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (accVal : B f x.l (guard + x.p)) (lossSum : ℕ),
      remSlots todo ≤ fuel →
      (∀ it ∈ todo, it.2.1.d + it.1 = D) →
      lossSum + A * remSlots todo ≤ guard →
      D4RankCode.Tree.total (fun lf => lf.weight * lf.doneProd η)
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel todo done accVal lossSum) =
      (2 : B f x.l (guard + x.p)) ^ (guard - lossSum - A * remSlots todo) * accVal *
        (done.map (SoloNode.pinnedVal hf (guard + x.p) η)).prod *
        (todo.map (itemExpSum hdeg η (guard + x.p) A)).prod := by
  intro D A fuel
  let q := guard + x.p
  have hsub_peel : ∀ xs : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc),
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
  induction fuel with
  | zero =>
    intro todo done accVal lossSum hfuel _ hloss
    have hrem0 : (peelCert todo).2 = [] := by
      rcases peelCert_rem_shape todo with h0 | ⟨k, nd, cert, sub, tail, hr⟩
      · exact h0
      · exfalso
        have hle := (peelCert_remSlots_le todo).trans hfuel
        rw [hr] at hle
        simp only [remSlots, List.map_cons, D4GuardTree.slots, List.sum_cons] at hle
        omega
    have hp_prod := peelCert_prod_eq hdeg η q A todo
    rw [hrem0] at hp_prod
    have hrem0_slots : remSlots ([] : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) = 0 := rfl
    rw [hrem0_slots, Nat.sub_zero, List.map_nil, List.prod_nil, mul_one] at hp_prod
    simp only [unrollCertFuel, D4RankCode.Tree.total, SoloLeafData.weight, SoloLeafData.doneProd,
      List.map_append, List.prod_append]
    have hp2 : (2 : B f x.l q) ^ (guard - lossSum) =
        (2 : B f x.l q) ^ (guard - lossSum - A * remSlots todo) *
          (2 : B f x.l q) ^ (A * remSlots todo) :=
      pow_add2 _ (by omega)
    dsimp only [q] at hp2 hp_prod ⊢
    rw [hp2, hp_prod]
    exact ring_leaf_rearrange _ _ _ _ _
  | succ fuel ih =>
    intro todo done accVal lossSum hfuel hdepth hloss
    have hp_prod := peelCert_prod_eq hdeg η q A todo
    have hrs_peel := peelCert_remSlots_le todo
    rcases peelCert_rem_shape todo with hrem0 | ⟨k, nd, cert, sub, tail, hrem⟩
    · rw [hrem0] at hp_prod
      have hrem0_slots : remSlots ([] : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) = 0 := rfl
      rw [hrem0_slots, Nat.sub_zero, List.map_nil, List.prod_nil, mul_one] at hp_prod
      simp only [unrollCertFuel, hrem0, D4RankCode.Tree.total, SoloLeafData.weight, SoloLeafData.doneProd,
        List.map_append, List.prod_append]
      have hp2 : (2 : B f x.l q) ^ (guard - lossSum) =
          (2 : B f x.l q) ^ (guard - lossSum - A * remSlots todo) *
            (2 : B f x.l q) ^ (A * remSlots todo) :=
        pow_add2 _ (by omega)
      dsimp only [q] at hp2 hp_prod ⊢
      rw [hp2, hp_prod]
      exact ring_leaf_rearrange _ _ _ _ _
    · simp only [unrollCertFuel, hrem, D4RankCode.Tree.total]
      let loss₀ := AppendixD4.loss nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) 0
      have hloss₀_le : loss₀ ≤ A :=
        loss_le_localAllowance x.S D nd.d nd.G.nE cert.hd.le cert.hM_le cert.hu_pos
      have hd_nd : nd.d + (k + 1) = D :=
        hdepth ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ (hsub_peel todo _ (by rw [hrem]; exact List.mem_cons_self))
      have hrs_rem : remSlots (peelCert todo).2 = 1 + 64 * D4GuardTree.slots k + remSlots tail := by
        rw [hrem]; simp [remSlots, D4GuardTree.slots, Nat.add_assoc]
      have hih_d : ∀ d : Fin cert.nBranches,
          let ν := cert.order d
          let w_val : B f x.l q :=
            lift hf q (AdjoinRoot.of _ (cert.s.weight ν.1 ν.2.1) : B f x.l (nd.pCurr + loss₀))
          let chList : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :=
            List.ofFn fun g : Fin 64 => ⟨k, cert.childNode ν g, sub ν g⟩
          D4RankCode.Tree.total (fun lf => lf.weight * lf.doneProd η)
            (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel
              (chList ++ tail) (done ++ (peelCert todo).1) (accVal * w_val) (lossSum + loss₀)) =
          ((2 : B f x.l q) ^ (guard - lossSum - A * remSlots todo) *
            (2 : B f x.l q) ^ (A * (remSlots todo - remSlots (peelCert todo).2)) *
            accVal * (done.map (SoloNode.pinnedVal hf q η)).prod *
            ((peelCert todo).1.map (SoloNode.pinnedVal hf q η)).prod *
            (tail.map (itemExpSum hdeg η q A)).prod) *
          ((2 : B f x.l q) ^ (A - loss₀) * w_val *
            ∏ g : Fin 64, itemExpSum hdeg η q A ⟨k, cert.childNode ν g, sub ν g⟩) := by
        intro d
        dsimp only
        let ν := cert.order d
        let w_val : B f x.l q :=
          lift hf q (AdjoinRoot.of _ (cert.s.weight ν.1 ν.2.1) : B f x.l (nd.pCurr + loss₀))
        let chList : List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc) :=
          List.ofFn fun g : Fin 64 => ⟨k, cert.childNode ν g, sub ν g⟩
        have hrs_next : remSlots (chList ++ tail) = 64 * D4GuardTree.slots k + remSlots tail :=
          active_children_remSlots k cert sub ν tail
        have hrec := ih (chList ++ tail) (done ++ (peelCert todo).1) (accVal * w_val) (lossSum + loss₀)
          (by rw [hrs_next]; omega)
          (fun it hit => by
            rcases List.mem_append.mp hit with hch | htl
            · obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hch
              change (nd.d + 1) + k = D; omega
            · exact hdepth it (hsub_peel todo it (by rw [hrem]; exact List.mem_cons_of_mem _ htl)))
          (by
            rw [hrs_next]
            have hmul_le : A * (1 + (64 * D4GuardTree.slots k + remSlots tail)) ≤ A * remSlots todo :=
              Nat.mul_le_mul_left _ (by omega)
            rw [Nat.mul_add, Nat.mul_one] at hmul_le
            omega)
        change D4RankCode.Tree.total (fun lf => lf.weight * lf.doneProd η)
          (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel
            (chList ++ tail) (done ++ (peelCert todo).1) (accVal * w_val) (lossSum + loss₀)) = _
        rw [hrec, hrs_next, List.map_append, List.prod_append, List.map_append, List.prod_append]
        have hch_prod : (chList.map (itemExpSum hdeg η q A)).prod =
            ∏ g : Fin 64, itemExpSum hdeg η q A ⟨k, cert.childNode ν g, sub ν g⟩ :=
          prod_map_ofFn 64 _ _
        dsimp only [q] at hch_prod
        rw [hch_prod]
        have hp_split : (2 : B f x.l q) ^ (guard - (lossSum + loss₀) - A * (64 * D4GuardTree.slots k + remSlots tail)) =
            (2 : B f x.l q) ^ (guard - lossSum - A * remSlots todo) *
            (2 : B f x.l q) ^ (A * (remSlots todo - remSlots (peelCert todo).2)) *
            (2 : B f x.l q) ^ (A - loss₀) := by
          apply pow_add3
          rw [hrs_rem]
          have hmul_peel : A * (remSlots todo - (1 + 64 * D4GuardTree.slots k + remSlots tail)) +
              (A + A * (64 * D4GuardTree.slots k + remSlots tail)) = A * remSlots todo := by
            have h1 : (remSlots todo - (1 + 64 * D4GuardTree.slots k + remSlots tail)) +
                (1 + (64 * D4GuardTree.slots k + remSlots tail)) = remSlots todo := by
              rw [hrs_rem] at hrs_peel; omega
            calc A * (remSlots todo - (1 + 64 * D4GuardTree.slots k + remSlots tail)) +
                  (A + A * (64 * D4GuardTree.slots k + remSlots tail))
                = A * (remSlots todo - (1 + 64 * D4GuardTree.slots k + remSlots tail)) +
                  A * (1 + (64 * D4GuardTree.slots k + remSlots tail)) := by ring
              _ = A * ((remSlots todo - (1 + 64 * D4GuardTree.slots k + remSlots tail)) +
                    (1 + (64 * D4GuardTree.slots k + remSlots tail))) := by
                    rw [← Nat.mul_add]
              _ = A * remSlots todo := congrArg (A * ·) h1
          omega
        dsimp only [q] at hp_split ⊢
        rw [hp_split]
        exact ring_step_rearrange _ _ _ _ _ _ _ _ _
      have hcongr_sum : (∑ d : Fin cert.nBranches,
          D4RankCode.Tree.total (fun lf => lf.weight * lf.doneProd η)
            (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard fuel
              ((List.ofFn fun g : Fin 64 => ⟨k, cert.childNode (cert.order d) g, sub (cert.order d) g⟩) ++ tail)
              (done ++ (peelCert todo).1)
              (accVal * lift hf q (AdjoinRoot.of _ (cert.s.weight (cert.order d).1 (cert.order d).2.1) : B f x.l (nd.pCurr + loss₀)))
              (lossSum + loss₀))) =
          ∑ d : Fin cert.nBranches,
            ((2 : B f x.l q) ^ (guard - lossSum - A * remSlots todo) *
              (2 : B f x.l q) ^ (A * (remSlots todo - remSlots (peelCert todo).2)) *
              accVal * (done.map (SoloNode.pinnedVal hf q η)).prod *
              ((peelCert todo).1.map (SoloNode.pinnedVal hf q η)).prod *
              (tail.map (itemExpSum hdeg η q A)).prod) *
            ((2 : B f x.l q) ^ (A - loss₀) *
              lift hf q (AdjoinRoot.of _ (cert.s.weight (cert.order d).1 (cert.order d).2.1) : B f x.l (nd.pCurr + loss₀)) *
              ∏ g : Fin 64, itemExpSum hdeg η q A ⟨k, cert.childNode (cert.order d) g, sub (cert.order d) g⟩) :=
        Finset.sum_congr rfl fun d _ => hih_d d
      dsimp only [q] at hcongr_sum
      rw [hcongr_sum, ← Finset.mul_sum]
      have hsum_order : (∑ d : Fin cert.nBranches,
          (2 : B f x.l q) ^ (A - loss₀) *
            lift hf q (AdjoinRoot.of _ (cert.s.weight (cert.order d).1 (cert.order d).2.1) : B f x.l (nd.pCurr + loss₀)) *
            ∏ g : Fin 64, itemExpSum hdeg η q A ⟨k, cert.childNode (cert.order d) g, sub (cert.order d) g⟩) =
          itemExpSum hdeg η q A ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ :=
        itemExpSum_step hdeg k cert sub hd_nd.le η q
      dsimp only [q] at hsum_order hp_prod ⊢
      rw [hsum_order]
      have hp_prod' : (todo.map (itemExpSum hdeg η (guard + x.p) A)).prod =
          (2 : B f x.l (guard + x.p)) ^ (A * (remSlots todo - remSlots (peelCert todo).2)) *
            ((peelCert todo).1.map (SoloNode.pinnedVal hf (guard + x.p) η)).prod *
            (itemExpSum hdeg η (guard + x.p) A ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ *
              (tail.map (itemExpSum hdeg η (guard + x.p) A)).prod) := by
        have h2 : ((peelCert todo).2.map (itemExpSum hdeg η (guard + x.p) A)).prod =
            itemExpSum hdeg η (guard + x.p) A ⟨k + 1, nd, PSum.inr ⟨cert, sub⟩⟩ *
              (tail.map (itemExpSum hdeg η (guard + x.p) A)).prod := by
          rw [hrem]; simp only [List.map_cons, List.prod_cons]
        exact hp_prod.trans (congrArg _ h2)
      rw [hp_prod']
      exact ring_step_finish _ _ _ _ _ _ _

private theorem heq_cast_B {f : ℤ[X]} {l p₁ p₂ : ℕ} (hp : p₁ = p₂) (z : B f l p₁) :
    HEq z (cast (congrArg (B f l) hp) z) := by
  subst hp; rfl

private def castExpansion {S l d₁ d₂ k p₁ p₂ : ℕ} {f : ℤ[X]} {hf : f.Monic}
    (hd : d₁ = d₂) (hp : p₁ = p₂) {z₁ : B f l p₁} {z₂ : B f l p₂} (hz : HEq z₁ z₂)
    (e : Expansion S f hf l d₁ k p₁ z₁) : Expansion S f hf l d₂ k p₂ z₂ := by
  subst hd; subst hp; cases hz; exact e

private theorem expSum_castExpansion {S l d₁ d₂ k p₁ p₂ : ℕ} {f : ℤ[X]} {hf : f.Monic}
    (hd : d₁ = d₂) (hp : p₁ = p₂) {z₁ : B f l p₁} {z₂ : B f l p₂} (hz : HEq z₁ z₂)
    (q A : ℕ) (e : Expansion S f hf l d₁ k p₁ z₁) :
    expSum q A (castExpansion hd hp hz e) = expSum q A e := by
  subst hd; subst hp; cases hz; rfl

private theorem lift_eq_of_heq {f : ℤ[X]} {hf : f.Monic} {l p₁ p₂ : ℕ} (hp : p₁ = p₂)
    {z₁ : B f l p₁} {z₂ : B f l p₂} (hz : HEq z₁ z₂) (q : ℕ) :
    lift hf q z₂ = lift hf q z₁ := by
  subst hp; cases hz; rfl

private theorem mul_pow_guard_expSum {S D l p : ℕ} {f : ℤ[X]} {hf : f.Monic}
    {z : B f l p} (e : Expansion S f hf l 0 D p z) :
    let guard := totalGuard S D
    let q := guard + p
    (2 : B f l q) ^ (guard - localAllowance S D * D4GuardTree.slots D) * expSum q (localAllowance S D) e =
      2 ^ guard * lift hf q z := by
  intro guard q
  unfold expSum
  rw [Finset.mul_sum]
  have hguard_le : localAllowance S D * D4GuardTree.slots D ≤ guard :=
    Nat.mul_le_mul_left _ (slots_bound_64 D)
  have hcomb : (∑ r : e.Ranks, (2 : B f l q) ^ (guard - localAllowance S D * D4GuardTree.slots D) *
      ((2 : B f l q) ^ (localAllowance S D * D4GuardTree.slots D - rawLossSum e r) *
        red f l q (rawCoeff e r) * e.leaves q r)) =
      ∑ r : e.Ranks, (2 : B f l q) ^ (guard - rawLossSum e r) *
        red f l q (rawCoeff e r) * e.leaves q r := by
    apply Finset.sum_congr rfl
    intro r _
    have hr_le : rawLossSum e r ≤ localAllowance S D * D4GuardTree.slots D :=
      rawLossSum_le_slots e (by omega) r
    have hexp_add : (guard - localAllowance S D * D4GuardTree.slots D) +
        (localAllowance S D * D4GuardTree.slots D - rawLossSum e r) =
        guard - rawLossSum e r := by omega
    rw [← mul_assoc, ← mul_assoc, ← pow_add2 (2 : B f l q) hexp_add.symm]
  rw [hcomb]
  exact (DetDLP.d4_raw_weight_cleared_identity e).2

/-- Root specialization: `Tree.total` on the root unrolling equals `2 ^ guard * SoloNode.pinnedVal`. -/
theorem root_unrollCert_total_eq {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
    (K_loc H_loc c_loc : ℕ)
    (rootNode : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf))
    (hd0 : rootNode.d = 0)
    (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
      (Nat.clog 32 (4 * x.m)) rootNode)
    (η : Fin (4 * x.m * x.k) → Bool) :
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let q := guard + x.p
    D4RankCode.Tree.total (fun lf => lf.weight * lf.doneProd η)
      (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
        [⟨D, rootNode, rootUnroll⟩] [] 1 0) =
    (2 : B f x.l q) ^ guard * SoloNode.pinnedVal hf q η rootNode := by
  intro D guard q
  let A := localAllowance x.S D
  have hp0 : rootNode.pCurr = x.p := by
    have hge := rootNode.hp_ge
    have hle := rootNode.hp_le
    rw [hd0] at hle
    simp at hle
    omega
  have hslots_le : D4GuardTree.slots D ≤ 64 ^ D := slots_bound_64 D
  have hguard_le : A * D4GuardTree.slots D ≤ guard :=
    Nat.mul_le_mul_left A hslots_le
  have htot := unrollCertFuel_total_eq x hf hdeg M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard η
    (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] 1 0
    (by simpa [remSlots] using hslots_le)
    (fun it hit => by rw [List.mem_singleton] at hit; subst hit; dsimp only; omega)
    (by simpa [remSlots] using hguard_le)
  dsimp only [D, A] at htot
  rw [htot]
  have hrs_root : remSlots ([⟨D, rootNode, rootUnroll⟩] :
      List (WorkCertItem x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc)) = D4GuardTree.slots D := by
    simp [remSlots]
  rw [hrs_root]
  simp only [Nat.sub_zero, mul_one, List.map_nil, List.prod_nil, List.map_singleton, List.prod_singleton]
  let z₁ : B f x.l rootNode.pCurr :=
    BTNContract rootNode.G (pin (rootNode.openTensor hf) (fun j => η (rootNode.pins.get j).1))
  let z₀ : B f x.l x.p := cast (congrArg (B f x.l) hp0) z₁
  have hz : HEq z₁ z₀ := heq_cast_B hp0 z₁
  let e₀ : Expansion x.S f hf x.l 0 D x.p z₀ :=
    castExpansion hd0 hp0 hz (SoloUnroll.toExpansion hdeg η D rootNode rootUnroll)
  have hexp_cast : itemExpSum hdeg η (guard + x.p) A ⟨D, rootNode, rootUnroll⟩ =
      expSum (guard + x.p) A e₀ :=
    (expSum_castExpansion hd0 hp0 hz (guard + x.p) A _).symm
  rw [hexp_cast, mul_pow_guard_expSum e₀]
  exact congrArg _ (lift_eq_of_heq hp0 hz _)


end
end DetDLP.M14TotalInternal

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic),
    0 < f.natDegree →
    ∀ (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
      (K_loc H_loc c_loc : ℕ)
      (rootNode : SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)),
      rootNode.d = 0 →
      ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc
          (Nat.clog 32 (4 * x.m)) rootNode)
        (η : Fin (4 * x.m * x.k) → Bool),
      let D := Nat.clog 32 (4 * x.m)
      let guard := totalGuard x.S D
      let q := guard + x.p
      D4RankCode.Tree.total (fun lf => lf.weight * lf.doneProd η)
        (unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
          [⟨D, rootNode, rootUnroll⟩] [] 1 0) =
      (2 : B f x.l q) ^ guard * SoloNode.pinnedVal hf q η rootNode := by
  intro C c x f hf hdeg M_node E_pkt o_node o_pkt K_loc H_loc c_loc rootNode hd0 rootUnroll η
  exact DetDLP.M14TotalInternal.root_unrollCert_total_eq x hf hdeg M_node E_pkt o_node o_pkt K_loc H_loc c_loc rootNode hd0 rootUnroll η
