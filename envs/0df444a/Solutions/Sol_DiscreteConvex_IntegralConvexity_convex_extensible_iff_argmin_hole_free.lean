-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexity.convex_extensible_iff_argmin_hole_free
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-02T12:31:10.059334+00:00
-- url     : https://prove2.me/submissions/763a01db-993f-46b3-aee2-90d6156b783c

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_ConvexExtensible
import Definitions.Def_DiscreteConvex_IntegralConvexity_ArgMinPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexity_HoleFree

namespace DiscreteConvex.IntegralConvexity.Prop318Aux

open DiscreteConvex.IntegralConvexity

open Finset

variable {n : ℕ}

/-- The convex hull of a finite set of real vectors is compact. -/
theorem finite_isCompact_convexHull' {s : Set (Fin n → ℝ)} (hs : s.Finite) :
    IsCompact (convexHull ℝ s) := by
  first
  | exact hs.isCompact_convexHull ℝ
  | exact hs.isCompact_convexHull

/-- Euclidean pairing `⟨p, v⟩`. -/
abbrev dotR (p v : Fin n → ℝ) : ℝ := ∑ i, p i * v i

/-- Real embedding of an integer point. -/
abbrev intToR (y : Fin n → ℤ) : Fin n → ℝ := fun i => (y i : ℝ)

theorem le_convexClosure' {f : (Fin n → ℤ) → WithTop ℝ} {v : Fin n → ℝ} (p : Fin n → ℝ) (α : ℝ)
    (h : ∀ y, ((α + dotR p (intToR y) : ℝ) : EReal) ≤ WithBot.some (f y)) :
    ((α + dotR p v : ℝ) : EReal) ≤ ConvexClosure f v :=
  le_sSup ⟨p, α, h, rfl⟩

theorem convexClosure_int_le (f : (Fin n → ℤ) → WithTop ℝ) (x : Fin n → ℤ) :
    ConvexClosure f (intToR x) ≤ WithBot.some (f x) := by
  apply sSup_le
  rintro v ⟨p, α, h, rfl⟩
  exact h x

/-! ### Forward direction -/

theorem holeFree_of_convexExtensible {f : (Fin n → ℤ) → WithTop ℝ} (hf : ConvexExtensible f)
    (p : Fin n → ℝ) : HoleFree (ArgMinPerturbed f p) := by
  intro y
  constructor
  · intro hy
    exact subset_convexHull ℝ _ ⟨y, hy, rfl⟩
  intro hyc
  set S := ArgMinPerturbed f p with hS
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.image_empty, convexHull_empty] at hyc
    exact hyc
  by_cases htop : ∃ s ∈ S, f s = ⊤
  · obtain ⟨s, hs, hfs⟩ := htop
    have hall : ∀ z, f z = ⊤ := by
      intro z
      have := hs z
      rw [hfs, top_add, top_le_iff] at this
      exact WithTop.add_eq_top.mp this |>.resolve_right WithTop.coe_ne_top
    intro z
    rw [hall z, top_add]
    exact le_top
  push_neg at htop
  obtain ⟨s0, hs0⟩ := hSne
  obtain ⟨a0, ha0⟩ := WithTop.ne_top_iff_exists.mp (htop s0 hs0)
  set m : ℝ := a0 - dotR p (intToR s0) with hm
  -- every point has value at least `m + ⟨p, ·⟩`
  have hlow : ∀ z (c : ℝ), f z = (c : WithTop ℝ) → m + dotR p (intToR z) ≤ c := by
    intro z c hz
    have := hs0 z
    rw [← ha0, hz] at this
    have h : a0 + dotR p (intToR z) ≤ c + dotR p (intToR s0) := by exact_mod_cast this
    simp only [hm]
    linarith
  -- points of `S` have value exactly `m + ⟨p, ·⟩`
  have hS_eq : ∀ s ∈ S, f s = ((m + dotR p (intToR s) : ℝ) : WithTop ℝ) := by
    intro s hs
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (htop s hs)
    have h1 := hlow s a ha.symm
    have := hs s0
    rw [← ha0, ← ha] at this
    have h2 : a + dotR p (intToR s0) ≤ a0 + dotR p (intToR s) := by exact_mod_cast this
    rw [← ha]
    congr 1
    simp only [hm]
    linarith
  -- the convex closure lies below `m + ⟨p, ·⟩` on the hull of `S`
  set H : Set (Fin n → ℝ) := {v | ∀ (q : Fin n → ℝ) (α : ℝ),
    (∀ w, ((α + dotR q (intToR w) : ℝ) : EReal) ≤ WithBot.some (f w)) →
      α + dotR q v ≤ m + dotR p v} with hH
  have hHconv : Convex ℝ H := by
    intro v1 hv1 v2 hv2 s t hs ht hst q α hq
    have h1 := hv1 q α hq
    have h2 := hv2 q α hq
    have e : ∀ r : Fin n → ℝ, dotR r (s • v1 + t • v2) = s * dotR r v1 + t * dotR r v2 := by
      intro r
      simp only [dotR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, e]
    have hα : α = s * α + t * α := by rw [← add_mul, hst, one_mul]
    have hm' : m = s * m + t * m := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
  have hSH : intToR '' S ⊆ H := by
    rintro _ ⟨s, hs, rfl⟩ q α hq
    have := hq s
    rw [hS_eq s hs] at this
    exact EReal.coe_le_coe_iff.mp this
  have hyH : intToR y ∈ H := convexHull_min hSH hHconv hyc
  have hcc : ConvexClosure f (intToR y) ≤ ((m + dotR p (intToR y) : ℝ) : EReal) := by
    apply sSup_le
    rintro v ⟨q, α, hq, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hyH q α hq)
  rw [hf y] at hcc
  have hfy : f y ≠ ⊤ := by
    intro h
    rw [h] at hcc
    exact WithTop.not_top_le_coe _ (WithBot.coe_le_coe.mp hcc)
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hfy
  rw [← hb] at hcc
  have hb' : b ≤ m + dotR p (intToR y) := EReal.coe_le_coe_iff.mp hcc
  intro z
  rw [← hb]
  cases hz : f z with
  | top => rw [top_add]; exact le_top
  | coe c =>
    have := hlow z c hz
    have h : b + dotR p (intToR z) ≤ c + dotR p (intToR y) := by linarith
    exact_mod_cast h

/-! ### The lower-face lemma -/

section LowerFace

variable {ι : Type*}

/-- `λ` represents `x` as a convex combination of the points `z y`, `y ∈ D`. -/
def IsRep (D : Finset ι) (z : ι → (Fin n → ℝ)) (x : Fin n → ℝ) (lam : ι → ℝ) : Prop :=
  (∀ y ∈ D, 0 ≤ lam y) ∧ ∑ y ∈ D, lam y = 1 ∧ ∑ y ∈ D, lam y • z y = x

theorem IsRep.smul_add {D : Finset ι} {z : ι → (Fin n → ℝ)} {x1 x2 : Fin n → ℝ}
    {l1 l2 : ι → ℝ} (h1 : IsRep D z x1 l1) (h2 : IsRep D z x2 l2) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hst : s + t = 1) : IsRep D z (s • x1 + t • x2) (s • l1 + t • l2) := by
  refine ⟨fun y hy => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (h1.1 y hy)) (mul_nonneg ht (h2.1 y hy))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      h1.2.1, h2.2.1, mul_one, hst]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
      mul_smul, ← Finset.smul_sum, h1.2.2, h2.2.2]

theorem exists_rep {D : Finset ι} {z : ι → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (z '' (D : Set ι))) : ∃ lam, IsRep D z x lam := by
  classical
  have hconv : Convex ℝ {v | ∃ lam, IsRep D z v lam} := by
    rintro v1 ⟨l1, h1⟩ v2 ⟨l2, h2⟩ s t hs ht hst
    exact ⟨_, h1.smul_add h2 hs ht hst⟩
  have hsub : z '' (D : Set ι) ⊆ {v | ∃ lam, IsRep D z v lam} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨fun w => if w = y then 1 else 0, fun w _ => by dsimp only; split_ifs <;> norm_num, ?_, ?_⟩
    · rw [Finset.sum_ite_eq' D y]; simp [Finset.mem_coe.mp hy]
    · simp only [ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_eq' D y]; simp [Finset.mem_coe.mp hy]
  exact convexHull_min hsub hconv hx

theorem mem_convexHull_of_weights {A : Finset ι} {z : ι → (Fin n → ℝ)} {x : Fin n → ℝ}
    {S : Set ι} (hAS : ∀ y ∈ A, y ∈ S) (w : ι → ℝ) (h0 : ∀ y ∈ A, 0 ≤ w y)
    (h1 : ∑ y ∈ A, w y = 1) (h2 : ∑ y ∈ A, w y • z y = x) : x ∈ convexHull ℝ (z '' S) := by
  rw [← h2]
  exact (convex_convexHull ℝ _).sum_mem h0 h1
    (fun y hy => subset_convexHull ℝ _ ⟨y, hAS y hy, rfl⟩)

theorem exists_maxRep {D : Finset ι} {z : ι → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (z '' (D : Set ι))) :
    ∃ lam, IsRep D z x lam ∧ ∀ nu, IsRep D z x nu → ∀ y ∈ D, 0 < nu y → 0 < lam y := by
  classical
  set S := D.powerset.filter (fun T => ∃ lam, IsRep D z x lam ∧ D.filter (fun y => 0 < lam y) = T)
  obtain ⟨lam0, h0⟩ := exists_rep hx
  have hSne : S.Nonempty :=
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), lam0, h0, rfl⟩⟩
  obtain ⟨T, hT, hTmax⟩ := S.exists_max_image Finset.card hSne
  obtain ⟨_, lam, hlam, hTeq⟩ := Finset.mem_filter.mp hT
  refine ⟨lam, hlam, fun nu hnu y hy hnuy => ?_⟩
  by_contra hlamy
  have hmid := hlam.smul_add hnu (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul] at hmid
  set mid := (1 / 2 : ℝ) • lam + (1 / 2 : ℝ) • nu
  have hsub : T ⊂ D.filter (fun w => 0 < mid w) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, ?_⟩
      · simp only [mid, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hlam.1 y hy
        linarith
      · rw [← hTeq]; simp [hlamy]
    · intro w hw
      rw [← hTeq] at hw
      obtain ⟨hwD, hw⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_filter.mpr ⟨hwD, ?_⟩
      simp only [mid, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hnu.1 w hwD
      linarith
  have hmem : D.filter (fun w => 0 < mid w) ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), mid, hmid, rfl⟩
  exact absurd (hTmax _ hmem) (not_le.mpr (Finset.card_lt_card hsub))

theorem clm_pi_decomp (φ : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    φ v = dotR (fun i => φ (fun j => if i = j then 1 else 0)) v := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotR, mul_comm]

theorem isRep_of_balanced {D : Finset ι} {z : ι → (Fin n → ℝ)} {x : Fin n → ℝ} (nu : ι → ℝ)
    (h0 : ∀ y ∈ D, 0 ≤ nu y) (hbal : ∑ y ∈ D, nu y • (z y - x) = 0)
    (hpos : 0 < ∑ y ∈ D, nu y) : IsRep D z x (fun y => nu y / ∑ w ∈ D, nu w) := by
  refine ⟨fun y hy => div_nonneg (h0 y hy) hpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hpos.ne']
  · have h1 : ∑ y ∈ D, nu y • z y = (∑ w ∈ D, nu w) • x := by
      have e : ∑ y ∈ D, nu y • (z y - x) = ∑ y ∈ D, nu y • z y - (∑ w ∈ D, nu w) • x := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun y _ => smul_sub _ _ _)
      rw [e, sub_eq_zero] at hbal
      exact hbal
    calc ∑ y ∈ D, (nu y / ∑ w ∈ D, nu w) • z y
          = (∑ w ∈ D, nu w)⁻¹ • ∑ y ∈ D, nu y • z y := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl (fun y _ => by rw [div_eq_inv_mul, mul_smul])
      _ = x := by rw [h1, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

theorem exists_gordan {D : Finset ι} {z : ι → (Fin n → ℝ)} {x : Fin n → ℝ} {lam : ι → ℝ}
    (hlam : IsRep D z x lam) (hmax : ∀ nu, IsRep D z x nu → ∀ y ∈ D, 0 < nu y → 0 < lam y) :
    ∃ q : Fin n → ℝ, (∀ y ∈ D, 0 < lam y → dotR q (z y - x) = 0) ∧
      (∀ y ∈ D, ¬ 0 < lam y → dotR q (z y - x) < 0) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, T = D.filter (fun y => 0 < lam y) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = D.filter (fun y => ¬ 0 < lam y) := ⟨_, rfl⟩
  let Lmap : (ι → ℝ) →ₗ[ℝ] (Fin n → ℝ) := ∑ y ∈ T, (LinearMap.proj y).smulRight (z y - x)
  have hLmap : ∀ ρ : ι → ℝ, Lmap ρ = ∑ y ∈ T, ρ y • (z y - x) := by
    intro ρ
    simp [Lmap, LinearMap.sum_apply]
  obtain ⟨L, hL⟩ : ∃ L, L = LinearMap.range Lmap := ⟨_, rfl⟩
  have hmemL : ∀ a, a ∈ L ↔ ∃ ρ : ι → ℝ, ∑ y ∈ T, ρ y • (z y - x) = a := by
    intro a
    rw [hL, LinearMap.mem_range]
    simp only [hLmap]
  obtain ⟨K, hK⟩ : ∃ K, K = convexHull ℝ ((fun y => z y - x) '' (U : Set ι)) := ⟨_, rfl⟩
  have hKc : IsCompact K := by rw [hK]; exact finite_isCompact_convexHull' (U.finite_toSet.image _)
  have hLc : IsClosed (L : Set (Fin n → ℝ)) := L.closed_of_finiteDimensional
  have hlamU : ∀ y ∈ U, lam y = 0 := by
    intro y hy
    rw [hU] at hy
    obtain ⟨hyD, hy⟩ := Finset.mem_filter.mp hy
    exact le_antisymm (not_lt.mp hy) (hlam.1 y hyD)
  have hlamT : ∀ y ∈ T, 0 < lam y := fun y hy => by rw [hT] at hy; exact (Finset.mem_filter.mp hy).2
  have hsplit : ∀ g : ι → Fin n → ℝ, ∑ y ∈ D, g y = ∑ y ∈ T, g y + ∑ y ∈ U, g y := by
    intro g
    rw [hT, hU, Finset.sum_filter_add_sum_filter_not]
  have hbal : ∑ y ∈ T, lam y • (z y - x) = 0 := by
    have h1 : ∑ y ∈ D, lam y • (z y - x) = 0 := by
      rw [show ∑ y ∈ D, lam y • (z y - x) = ∑ y ∈ D, lam y • z y - (∑ y ∈ D, lam y) • x by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun y _ => smul_sub _ _ _), hlam.2.1, hlam.2.2, one_smul,
        sub_self]
    rw [hsplit, Finset.sum_eq_zero (s := U) (fun y hy => by rw [hlamU y hy, zero_smul]),
      add_zero] at h1
    exact h1
  have hdisj : Disjoint K L := by
    rw [Set.disjoint_left]
    intro a haK haL
    rw [hK] at haK
    obtain ⟨κ, hκ0, hκ1, hκ2⟩ := exists_rep (z := fun y => z y - x) haK
    obtain ⟨ρ, hρ⟩ := (hmemL a).mp haL
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ y ∈ T, |ρ y| / lam y := ⟨_, rfl⟩
    have hMy : ∀ y ∈ T, ρ y ≤ M * lam y := by
      intro y hy
      have h1 : |ρ y| / lam y ≤ M := by
        rw [hM]
        exact Finset.single_le_sum (f := fun y => |ρ y| / lam y)
          (fun w hw => div_nonneg (abs_nonneg _) (hlamT w hw).le) hy
      have h2 := hlamT y hy
      rw [div_le_iff₀ h2] at h1
      linarith [le_abs_self (ρ y)]
    let nu' : ι → ℝ := fun y => if 0 < lam y then M * lam y - ρ y else κ y
    have hnuT : ∀ y ∈ T, nu' y = M * lam y - ρ y := fun y hy => if_pos (hlamT y hy)
    have hnuU : ∀ y ∈ U, nu' y = κ y := fun y hy => by
      rw [hU] at hy
      exact if_neg (Finset.mem_filter.mp hy).2
    have hsplitR : ∀ g : ι → ℝ, ∑ y ∈ D, g y = ∑ y ∈ T, g y + ∑ y ∈ U, g y := by
      intro g
      rw [hT, hU, Finset.sum_filter_add_sum_filter_not]
    have hN : 1 ≤ ∑ y ∈ D, nu' y := by
      rw [hsplitR, Finset.sum_congr rfl hnuU, hκ1]
      have : 0 ≤ ∑ y ∈ T, nu' y :=
        Finset.sum_nonneg (fun y hy => by rw [hnuT y hy]; linarith [hMy y hy])
      linarith
    have hcomb : ∑ y ∈ D, nu' y • (z y - x) = 0 := by
      rw [hsplit]
      have hUpart : ∑ y ∈ U, nu' y • (z y - x) = a := by
        rw [← hκ2]
        exact Finset.sum_congr rfl (fun y hy => by rw [hnuU y hy])
      have hTpart : ∑ y ∈ T, nu' y • (z y - x) = -a := by
        rw [Finset.sum_congr rfl (fun y hy => show nu' y • (z y - x) =
          (M * lam y - ρ y) • (z y - x) by rw [hnuT y hy])]
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
        rw [← Finset.smul_sum, hbal, smul_zero, hρ, zero_sub]
      rw [hUpart, hTpart, neg_add_cancel]
    have hnu := isRep_of_balanced nu' (fun y hy => by
        rw [hsplitR] at hN
        by_cases h : 0 < lam y
        · rw [show nu' y = M * lam y - ρ y from if_pos h]
          have hyT : y ∈ T := by rw [hT]; exact Finset.mem_filter.mpr ⟨hy, h⟩
          linarith [hMy y hyT]
        · rw [show nu' y = κ y from if_neg h]
          exact hκ0 y (by rw [hU]; exact Finset.mem_filter.mpr ⟨hy, h⟩)) hcomb (by linarith)
    obtain ⟨y, hyU, hκy⟩ : ∃ y ∈ U, 0 < κ y := by
      by_contra hcon
      push_neg at hcon
      have := Finset.sum_nonpos hcon
      linarith
    have hyU' := hyU
    rw [hU] at hyU'
    obtain ⟨hyD, hy⟩ := Finset.mem_filter.mp hyU'
    apply hy
    apply hmax _ hnu y hyD
    rw [hnuU y hyU]
    exact div_pos hκy (by linarith)
  obtain ⟨φ, u, v, hu, huv, hv⟩ :=
    geometric_hahn_banach_compact_closed (by rw [hK]; exact convex_convexHull ℝ _) hKc
      L.convex hLc hdisj
  have hφL : ∀ b ∈ L, φ b = 0 := by
    intro b hb
    by_contra hne
    have hmem : ((v - 1) / φ b) • b ∈ L := L.smul_mem _ hb
    have := hv _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
    linarith
  have hv0 : v < 0 := by
    have := hv 0 L.zero_mem
    rwa [map_zero] at this
  refine ⟨fun i => φ (fun j => if i = j then 1 else 0), fun y hy hpos => ?_, fun y hy hpos => ?_⟩
  · rw [← clm_pi_decomp]
    apply hφL
    rw [hmemL]
    refine ⟨fun w => if w = y then 1 else 0, ?_⟩
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' T y]
    rw [if_pos (by rw [hT]; exact Finset.mem_filter.mpr ⟨hy, hpos⟩)]
  · rw [← clm_pi_decomp]
    have := hu _ (by rw [hK]; exact subset_convexHull ℝ _ ⟨y, by
      rw [hU]; exact Finset.mem_filter.mpr ⟨hy, hpos⟩, rfl⟩)
    linarith

theorem dotR_add_smul (p d : Fin n → ℝ) (t : ℝ) (v : Fin n → ℝ) :
    dotR (fun i => p i + t * d i) v = dotR p v + t * dotR d v := by
  simp only [dotR, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem dotR_sub (p v w : Fin n → ℝ) : dotR p (v - w) = dotR p v - dotR p w := by
  simp only [dotR, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- First-order optimality: at a maximizer of the lower-face problem, `x` lies in the convex hull
of the active points. -/
theorem opt_condition (T : Finset ι) (hT : T.Nonempty) (z : ι → (Fin n → ℝ)) (c : ι → ℝ)
    (x : Fin n → ℝ) (p : Fin n → ℝ) (m : ℝ) (hfeas : ∀ y ∈ T, m + dotR p (z y - x) ≤ c y)
    (hmax : ∀ (p' : Fin n → ℝ) (m' : ℝ), (∀ y ∈ T, m' + dotR p' (z y - x) ≤ c y) → m' ≤ m) :
    x ∈ convexHull ℝ (z '' {y | y ∈ T ∧ m + dotR p (z y - x) = c y}) := by
  classical
  by_contra hx
  set Act := T.filter (fun y => m + dotR p (z y - x) = c y) with hAct
  have hset : {y | y ∈ T ∧ m + dotR p (z y - x) = c y} = (Act : Set ι) := by
    ext y; simp [hAct]
  rw [hset] at hx
  have hcl : IsClosed (convexHull ℝ (z '' (Act : Set ι))) :=
    (finite_isCompact_convexHull' (Act.finite_toSet.image z)).isClosed
  obtain ⟨φ, u, hφ, hφx⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hcl hx
  set d : Fin n → ℝ := fun i => φ (fun j => if i = j then 1 else 0) with hd
  have he : ∀ y ∈ Act, dotR d (z y - x) < 0 := by
    intro y hy
    have h1 := hφ (z y) (subset_convexHull ℝ _ ⟨y, hy, rfl⟩)
    rw [dotR_sub, ← clm_pi_decomp, ← clm_pi_decomp]
    linarith
  set δ := T.inf' hT (fun y => if y ∈ Act then -dotR d (z y - x) else 1) with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro y hy
    split_ifs with h
    · linarith [he y h]
    · exact one_pos
  have hδle : ∀ y ∈ Act, δ ≤ -dotR d (z y - x) := by
    intro y hy
    have := Finset.inf'_le (fun y => if y ∈ Act then -dotR d (z y - x) else 1)
      (Finset.mem_filter.mp hy).1
    rwa [if_pos hy] at this
  set slack : ι → ℝ := fun y => c y - m - dotR p (z y - x) with hslack
  have hslack_pos : ∀ y ∈ T, y ∉ Act → 0 < slack y := by
    intro y hy hna
    have h1 := hfeas y hy
    have h2 : m + dotR p (z y - x) ≠ c y := fun h => hna (Finset.mem_filter.mpr ⟨hy, h⟩)
    simp only [hslack]
    have := lt_of_le_of_ne h1 h2
    linarith
  set t := T.inf' hT (fun y => if y ∈ Act then 1 else slack y / (|δ + dotR d (z y - x)| + 1))
    with ht
  have htpos : 0 < t := by
    rw [ht, Finset.lt_inf'_iff]
    intro y hy
    split_ifs with h
    · exact one_pos
    · exact div_pos (hslack_pos y hy h) (by positivity)
  have hfeas' : ∀ y ∈ T, (m + t * δ) + dotR (fun i => p i + t * d i) (z y - x) ≤ c y := by
    intro y hy
    rw [dotR_add_smul]
    have key : t * (δ + dotR d (z y - x)) ≤ slack y := by
      by_cases h : y ∈ Act
      · have h1 := hδle y h
        have h2 : slack y = 0 := by
          simp only [hslack]
          have := (Finset.mem_filter.mp h).2
          linarith
        rw [h2]
        nlinarith
      · have h1 : t ≤ slack y / (|δ + dotR d (z y - x)| + 1) := by
          have := Finset.inf'_le
            (fun y => if y ∈ Act then 1 else slack y / (|δ + dotR d (z y - x)| + 1)) hy
          rwa [if_neg h] at this
        have hs := hslack_pos y hy h
        have hA : 0 < |δ + dotR d (z y - x)| + 1 := by positivity
        rw [le_div_iff₀ hA] at h1
        have := le_abs_self (δ + dotR d (z y - x))
        nlinarith [abs_nonneg (δ + dotR d (z y - x))]
    simp only [hslack] at key
    linarith
  have := hmax _ _ hfeas'
  nlinarith

theorem exists_max_point (T : Finset ι) (hT : T.Nonempty) (z : ι → (Fin n → ℝ))
    (c : ι → ℝ) (x : Fin n → ℝ) (lam : ι → ℝ) (hpos : ∀ y ∈ T, 0 < lam y)
    (hsum : ∑ y ∈ T, lam y = 1) (hcomb : ∑ y ∈ T, lam y • z y = x) :
    ∃ (p : Fin n → ℝ) (m : ℝ), (∀ y ∈ T, m + dotR p (z y - x) ≤ c y) ∧
      ∀ (p' : Fin n → ℝ) (m' : ℝ), (∀ y ∈ T, m' + dotR p' (z y - x) ≤ c y) → m' ≤ m := by
  classical
  -- the linear map `p ↦ (⟨p, z y - x⟩)_{y ∈ T}`
  let A : (Fin n → ℝ) →ₗ[ℝ] (T → ℝ) :=
    { toFun := fun p y => dotR p (z y - x)
      map_add' := fun p q => by
        funext y
        simp only [dotR, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r p => by
        funext y
        simp only [dotR, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hA : ∀ p (y : T), A p y = dotR p (z y - x) := fun _ _ => rfl
  set V := LinearMap.range A with hV
  set g0 := T.inf' hT c with hg0
  set Cmax := T.sup' hT c with hCmax
  set lmin := T.inf' hT lam with hlmin
  have hg0le : ∀ y ∈ T, g0 ≤ c y := fun y hy => Finset.inf'_le c hy
  have hCle : ∀ y ∈ T, c y ≤ Cmax := fun y hy => Finset.le_sup' c hy
  have hlminpos : 0 < lmin := by
    rw [hlmin, Finset.lt_inf'_iff]; exact hpos
  have hlminle : ∀ y ∈ T, lmin ≤ lam y := fun y hy => Finset.inf'_le lam hy
  obtain ⟨y0, hy0⟩ := hT
  set B := Cmax - g0 with hB
  have hB0 : 0 ≤ B := by linarith [hg0le y0 hy0, hCle y0 hy0]
  -- balance: `∑ λ_y ⟨p, z y - x⟩ = 0`
  have hbal0 : ∑ y ∈ T, lam y • (z y - x) = 0 := by
    rw [show ∑ y ∈ T, lam y • (z y - x) = ∑ y ∈ T, lam y • z y - (∑ y ∈ T, lam y) • x by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun y _ => smul_sub _ _ _), hsum, hcomb, one_smul, sub_self]
  have hbal : ∀ p, ∑ y : T, lam y * A p y = 0 := by
    intro p
    have : ∑ y : T, lam y * A p y = dotR p (∑ y ∈ T, lam y • (z y - x)) := by
      show ∑ y : T, lam y * dotR p (z y - x) = _
      rw [Finset.sum_coe_sort T (fun y => lam y * dotR p (z y - x))]
      simp only [dotR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun y _ => by ring))
    rw [this, hbal0]
    simp [dotR]
  have hsumT : ∑ y : T, lam y = 1 := by rw [Finset.sum_coe_sort T lam]; exact hsum
  -- the feasible set
  set S : Set ((T → ℝ) × ℝ) :=
    {pr | pr.1 ∈ V ∧ (∀ y : T, pr.2 + pr.1 y ≤ c y) ∧ g0 ≤ pr.2} with hS
  have hSclosed : IsClosed S := by
    have h1 : IsClosed {pr : (T → ℝ) × ℝ | pr.1 ∈ V} :=
      V.closed_of_finiteDimensional.preimage continuous_fst
    have h2 : IsClosed {pr : (T → ℝ) × ℝ | ∀ y : T, pr.2 + pr.1 y ≤ c y} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter (fun y => isClosed_le (by fun_prop) continuous_const)
    have h3 : IsClosed {pr : (T → ℝ) × ℝ | g0 ≤ pr.2} := isClosed_le continuous_const continuous_snd
    have : S = {pr : (T → ℝ) × ℝ | pr.1 ∈ V} ∩ {pr | ∀ y : T, pr.2 + pr.1 y ≤ c y} ∩
        {pr | g0 ≤ pr.2} := by
      ext pr; simp [hS, and_assoc]
    rw [this]
    exact (h1.inter h2).inter h3
  -- a priori bounds on feasible points
  have hbound : ∀ pr ∈ S, (∀ y : T, |pr.1 y| ≤ B + B / lmin) ∧ |pr.2| ≤ |g0| + |Cmax| + B + B / lmin := by
    rintro ⟨w, m⟩ ⟨⟨p, rfl⟩, hfe, hg⟩
    simp only at hfe hg ⊢
    have hup : ∀ y : T, A p y ≤ B := fun y => by
      have := hfe y
      have := hCle y y.2
      linarith
    have hlow : ∀ y : T, -(B / lmin) ≤ A p y := by
      intro y
      have hsplit := hbal p
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y)] at hsplit
      have hrest : ∑ w ∈ Finset.univ.erase y, lam w * A p w ≤ B := by
        calc ∑ w ∈ Finset.univ.erase y, lam w * A p w ≤ ∑ w ∈ Finset.univ.erase y, lam w * B :=
              Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hup w) (hpos w w.2).le)
          _ ≤ ∑ w : T, lam w * B := Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.erase_subset _ _) (fun w _ _ => mul_nonneg (hpos w w.2).le hB0)
          _ = B := by rw [← Finset.sum_mul, hsumT, one_mul]
      have hy : -B ≤ lam y * A p y := by linarith
      have hly := hpos y y.2
      have hlm := hlminle y y.2
      have h1 : -B / lam y ≤ A p y := by rw [div_le_iff₀ hly]; linarith
      have h2 : -(B / lmin) ≤ -B / lam y := by
        rw [neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left hB0 hlminpos hlm
      linarith
    have hBl : 0 ≤ B / lmin := div_nonneg hB0 hlminpos.le
    refine ⟨fun y => abs_le.mpr ⟨by linarith [hlow y], by linarith [hup y]⟩, ?_⟩
    have := hfe ⟨y0, hy0⟩
    have := hlow ⟨y0, hy0⟩
    have := hCle y0 hy0
    have := le_abs_self g0
    have := neg_abs_le g0
    have := le_abs_self Cmax
    have := abs_nonneg Cmax
    rw [abs_le]
    constructor <;> linarith
  have hSbdd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max (B + B / lmin) (|g0| + |Cmax| + B + B / lmin), fun pr hpr => ?_⟩
    obtain ⟨h1, h2⟩ := hbound pr hpr
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    apply max_le_max
    · have hB' : 0 ≤ B + B / lmin := by
        have := div_nonneg hB0 hlminpos.le; linarith
      exact (pi_norm_le_iff_of_nonneg hB').mpr (fun y => by rw [Real.norm_eq_abs]; exact h1 y)
    · rw [Real.norm_eq_abs]; exact h2
  have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
  have hSne : S.Nonempty := ⟨(0, g0), ⟨V.zero_mem, fun y => by simp [hg0le y y.2], le_rfl⟩⟩
  obtain ⟨⟨w, m⟩, hmem, hmax⟩ := hScomp.exists_isMaxOn hSne continuous_snd.continuousOn
  obtain ⟨⟨p, rfl⟩, hfe, hg⟩ := hmem
  refine ⟨p, m, fun y hy => hfe ⟨y, hy⟩, fun p' m' hfe' => ?_⟩
  by_cases hm' : m' < g0
  · exact (hm'.trans_le hg).le
  · push_neg at hm'
    have hmem' : (A p', m') ∈ S := ⟨⟨p', rfl⟩, fun y => hfe' y y.2, hm'⟩
    exact hmax hmem'

theorem exists_opt_on_support (T : Finset ι) (hT : T.Nonempty) (z : ι → (Fin n → ℝ))
    (c : ι → ℝ) (x : Fin n → ℝ) (lam : ι → ℝ) (hpos : ∀ y ∈ T, 0 < lam y)
    (hsum : ∑ y ∈ T, lam y = 1) (hcomb : ∑ y ∈ T, lam y • z y = x) :
    ∃ (p : Fin n → ℝ) (m : ℝ), (∀ y ∈ T, m + dotR p (z y - x) ≤ c y) ∧
      x ∈ convexHull ℝ (z '' {y | y ∈ T ∧ m + dotR p (z y - x) = c y}) := by
  obtain ⟨p, m, hfeas, hmax⟩ := exists_max_point T hT z c x lam hpos hsum hcomb
  exact ⟨p, m, hfeas, opt_condition T hT z c x p m hfeas hmax⟩

theorem dotR_shift (p q : Fin n → ℝ) (K m : ℝ) (v x : Fin n → ℝ) :
    (m - dotR (fun i => p i + K * q i) x) + dotR (fun i => p i + K * q i) v =
      m + dotR p (v - x) + K * dotR q (v - x) := by
  simp only [dotR, Pi.sub_apply, mul_sub, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]
  ring

/-- Every point of the convex hull of finitely many lifted points lies in the projection of a
lower face. -/
theorem exists_lower_face (D : Finset ι) (z : ι → (Fin n → ℝ)) (c : ι → ℝ) (x : Fin n → ℝ)
    (hx : x ∈ convexHull ℝ (z '' (D : Set ι))) :
    ∃ (p : Fin n → ℝ) (m : ℝ), (∀ y ∈ D, m + dotR p (z y) ≤ c y) ∧
      x ∈ convexHull ℝ (z '' {y | y ∈ D ∧ m + dotR p (z y) = c y}) := by
  classical
  obtain ⟨lam, hlam, hmax⟩ := exists_maxRep hx
  obtain ⟨q, hq0, hqneg⟩ := exists_gordan hlam hmax
  obtain ⟨T, hT⟩ : ∃ T, T = D.filter (fun y => 0 < lam y) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = D.filter (fun y => ¬ 0 < lam y) := ⟨_, rfl⟩
  have hlamT : ∀ y ∈ T, 0 < lam y := fun y hy => by rw [hT] at hy; exact (Finset.mem_filter.mp hy).2
  have hlamU : ∀ y ∈ U, lam y = 0 := by
    intro y hy
    rw [hU] at hy
    obtain ⟨hyD, hy⟩ := Finset.mem_filter.mp hy
    exact le_antisymm (not_lt.mp hy) (hlam.1 y hyD)
  have hsum : ∑ y ∈ T, lam y = 1 := by
    have := hlam.2.1
    rw [← Finset.sum_filter_add_sum_filter_not D (fun y => 0 < lam y), ← hT, ← hU,
      Finset.sum_eq_zero (s := U) hlamU, add_zero] at this
    exact this
  have hcomb : ∑ y ∈ T, lam y • z y = x := by
    have := hlam.2.2
    rw [← Finset.sum_filter_add_sum_filter_not D (fun y => 0 < lam y), ← hT, ← hU,
      Finset.sum_eq_zero (s := U) (fun y hy => by rw [hlamU y hy, zero_smul]), add_zero] at this
    exact this
  have hTne : T.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  obtain ⟨p, m, hle, hmem⟩ := exists_opt_on_support T hTne z c x lam hlamT hsum hcomb
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ y ∈ U, |m + dotR p (z y - x) - c y| / (-dotR q (z y - x)) :=
    ⟨_, rfl⟩
  have hqU : ∀ y ∈ U, dotR q (z y - x) < 0 := fun y hy => by
    rw [hU] at hy
    obtain ⟨hyD, hy⟩ := Finset.mem_filter.mp hy
    exact hqneg y hyD hy
  have hqT : ∀ y ∈ T, dotR q (z y - x) = 0 := fun y hy => by
    rw [hT] at hy
    obtain ⟨hyD, hy⟩ := Finset.mem_filter.mp hy
    exact hq0 y hyD hy
  have hKy : ∀ y ∈ U, m + dotR p (z y - x) + K * dotR q (z y - x) ≤ c y := by
    intro y hy
    have hneg := hqU y hy
    have h1 : |m + dotR p (z y - x) - c y| / (-dotR q (z y - x)) ≤ K := by
      rw [hK]
      exact Finset.single_le_sum (f := fun y => |m + dotR p (z y - x) - c y| / (-dotR q (z y - x)))
        (fun w hw => div_nonneg (abs_nonneg _) (by linarith [hqU w hw])) hy
    rw [div_le_iff₀ (by linarith)] at h1
    have := le_abs_self (m + dotR p (z y - x) - c y)
    nlinarith
  refine ⟨fun i => p i + K * q i, m - dotR (fun i => p i + K * q i) x, fun y hy => ?_, ?_⟩
  · rw [dotR_shift]
    by_cases h : 0 < lam y
    · have hyT : y ∈ T := by rw [hT]; exact Finset.mem_filter.mpr ⟨hy, h⟩
      rw [hqT y hyT, mul_zero, add_zero]
      exact hle y hyT
    · exact hKy y (by rw [hU]; exact Finset.mem_filter.mpr ⟨hy, h⟩)
  · refine convexHull_mono (Set.image_mono ?_) hmem
    rintro y ⟨hyT, hyeq⟩
    refine ⟨?_, ?_⟩
    · rw [hT] at hyT; exact (Finset.mem_filter.mp hyT).1
    · rw [dotR_shift, hqT y hyT, mul_zero, add_zero]
      exact hyeq

end LowerFace

/-! ### Backward direction -/

theorem domZ_finite {f : (Fin n → ℤ) → WithTop ℝ}
    (hbdd : ∃ R : ℝ, ∀ x : Fin n → ℤ, f x ≠ ⊤ → ∀ i, |(x i : ℝ)| ≤ R) :
    {y | f y ≠ ⊤}.Finite := by
  obtain ⟨R, hR⟩ := hbdd
  apply (Set.finite_Icc (fun _ : Fin n => -⌈R⌉) (fun _ => ⌈R⌉)).subset
  intro y hy
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h := (abs_le.mp (hR y hy i)).1
    have : (-(⌈R⌉ : ℝ)) ≤ (y i : ℝ) := by linarith [Int.le_ceil R]
    exact_mod_cast this
  · have h := (abs_le.mp (hR y hy i)).2
    have : (y i : ℝ) ≤ (⌈R⌉ : ℝ) := by linarith [Int.le_ceil R]
    exact_mod_cast this

theorem convexExtensible_of_holeFree {f : (Fin n → ℤ) → WithTop ℝ}
    (hbdd : ∃ R : ℝ, ∀ x : Fin n → ℤ, f x ≠ ⊤ → ∀ i, |(x i : ℝ)| ≤ R)
    (hhole : ∀ p : Fin n → ℝ, HoleFree (ArgMinPerturbed f p)) : ConvexExtensible f := by
  classical
  intro x
  apply le_antisymm (convexClosure_int_le f x)
  set D : Finset (Fin n → ℤ) := (domZ_finite hbdd).toFinset with hD
  have hmemD : ∀ y, y ∈ D ↔ f y ≠ ⊤ := fun y => by simp [hD]
  set c : (Fin n → ℤ) → ℝ := fun y => (f y).untopD 0 with hc
  have hfc : ∀ y ∈ D, f y = (c y : WithTop ℝ) := by
    intro y hy
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((hmemD y).mp hy)
    simp [hc, ← ha]
  have hftop : ∀ y, y ∉ D → f y = ⊤ := fun y hy => by simpa [hmemD] using hy
  by_cases hx : intToR x ∈ convexHull ℝ (intToR '' (D : Set (Fin n → ℤ)))
  · obtain ⟨p, m, hle, hmem⟩ := exists_lower_face D intToR c (intToR x) hx
    set A := {y | y ∈ D ∧ m + dotR p (intToR y) = c y} with hA
    have hAarg : A ⊆ ArgMinPerturbed f p := by
      rintro y ⟨hyD, hyeq⟩ w
      rw [hfc y hyD]
      by_cases hw : w ∈ D
      · rw [hfc w hw]
        have := hle w hw
        have h : c y + dotR p (intToR w) ≤ c w + dotR p (intToR y) := by linarith
        exact_mod_cast h
      · rw [hftop w hw]
        simp
    have hmem' : intToR x ∈ convexHull ℝ (intToR '' ArgMinPerturbed f p) :=
      convexHull_mono (Set.image_mono hAarg) hmem
    have hxarg := (hhole p x).mpr hmem'
    have hAne : A.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, Set.image_empty, convexHull_empty] at hmem
      exact hmem
    obtain ⟨y0, hy0D, hy0eq⟩ := hAne
    have h0 := hxarg y0
    rw [hfc y0 hy0D] at h0
    have hxD : x ∈ D := by
      rw [hmemD]
      intro htop
      rw [htop, top_add, top_le_iff, ← WithTop.coe_add] at h0
      exact WithTop.coe_ne_top h0
    rw [hfc x hxD] at h0 ⊢
    have h0' : c x + dotR p (intToR y0) ≤ c y0 + dotR p (intToR x) := by exact_mod_cast h0
    have hcc := le_convexClosure' (f := f) (v := intToR x) p m (fun y => by
      by_cases hy : y ∈ D
      · rw [hfc y hy]
        exact EReal.coe_le_coe_iff.mpr (hle y hy)
      · rw [hftop y hy]; exact le_top)
    refine le_trans ?_ hcc
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  · have hcl : IsClosed (convexHull ℝ (intToR '' (D : Set (Fin n → ℤ)))) :=
      (finite_isCompact_convexHull' (D.finite_toSet.image _)).isClosed
    obtain ⟨φ, u, hφ, hφx⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hcl hx
    set d : Fin n → ℝ := fun i => φ (fun j => if i = j then 1 else 0)
    obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, ∀ y ∈ D, c0 ≤ c y := by
      obtain ⟨c0, hc0⟩ := (D.image c).bddBelow
      exact ⟨c0, fun y hy => hc0 (Finset.mem_coe.mpr (Finset.mem_image_of_mem c hy))⟩
    have htop : ConvexClosure f (intToR x) = ⊤ := by
      rw [EReal.eq_top_iff_forall_lt]
      intro M
      have hgap : 0 < φ (intToR x) - u := by linarith
      set K : ℝ := (|M - c0| + 1) / (φ (intToR x) - u)
      have hK : 0 ≤ K := by positivity
      have hKx : K * (φ (intToR x) - u) = |M - c0| + 1 := by
        simp only [K]; field_simp
      have hcc := le_convexClosure' (f := f) (v := intToR x) (fun i => K * d i) (c0 - K * u)
        (fun y => by
          by_cases hy : y ∈ D
          · rw [hfc y hy]
            apply EReal.coe_le_coe_iff.mpr
            have h1 := hφ (intToR y) (subset_convexHull ℝ _ ⟨y, hy, rfl⟩)
            rw [clm_pi_decomp] at h1
            have h2 : dotR (fun i => K * d i) (intToR y) = K * dotR d (intToR y) := by
              simp only [dotR, Finset.mul_sum, mul_assoc]
            rw [h2]
            have := hc0 y hy
            nlinarith
          · rw [hftop y hy]; exact le_top)
      refine lt_of_lt_of_le ?_ hcc
      apply EReal.coe_lt_coe_iff.mpr
      have h2 : dotR (fun i => K * d i) (intToR x) = K * φ (intToR x) := by
        rw [clm_pi_decomp φ]
        simp only [dotR, Finset.mul_sum, mul_assoc, d]
      rw [h2]
      have := le_abs_self (M - c0)
      nlinarith
    rw [htop]
    exact le_top

end DiscreteConvex.IntegralConvexity.Prop318Aux

open DiscreteConvex.IntegralConvexity DiscreteConvex.IntegralConvexity.Prop318Aux

/-- Proposition 3.18 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.93). -/
theorem solution {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) :
    (ConvexExtensible f → ∀ p : Fin n → ℝ, HoleFree (ArgMinPerturbed f p)) ∧
    ((∃ R : ℝ, ∀ x : Fin n → ℤ, f x ≠ ⊤ → ∀ i, |(x i : ℝ)| ≤ R) →
      (∀ p : Fin n → ℝ, HoleFree (ArgMinPerturbed f p)) → ConvexExtensible f) :=
  ⟨fun hf p => holeFree_of_convexExtensible hf p,
    fun hbdd hhole => convexExtensible_of_holeFree hbdd hhole⟩

