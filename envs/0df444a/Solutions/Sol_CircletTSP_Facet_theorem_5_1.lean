-- Prove2me | solution 1 for CircletTSP.Facet.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:04:35.043984+00:00
-- url     : https://prove2.me/submissions/9cfbbb67-f43c-44c0-bb66-369d89270878

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_CircletTSP_Facet_Setting
import Theorems.Thm_CircletTSP_Facet_theorem_3_1
import Theorems.Thm_CircletTSP_Facet_stsp_dim
import Theorems.Thm_CircletTSP_Facet_tight_tours

set_option autoImplicit false

open CircletTSP.Facet


open scoped BigOperators

namespace CircletTSP.Facet.TourCounts

lemma rotate_ne_self {n : ℕ} (hn : 1 < n) (i : Fin n) : finRotate n i ≠ i := by
  cases n with
  | zero => omega
  | succ n =>
    intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    by_cases hi : i = Fin.last n
    · subst i
      simp at hv
      omega
    · simp [hi] at hv

lemma tourVec_nonneg {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    0 ≤ MetricTSP.tourVec π u v := by
  unfold MetricTSP.tourVec
  positivity

lemma tourVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = MetricTSP.tourVec π v u := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps, or_comm]

lemma tourVec_eq_step_sum {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = ∑ k : Fin n,
      if (π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u)
      then (1 : ℝ) else 0 := by
  unfold MetricTSP.tourVec MetricTSP.tourSteps
  exact Finset.natCast_card_filter _ _

lemma single_edge_mass_of_lt {n : ℕ} (a b : Fin n) (hab : a < b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then (1 : ℝ) else 0) = 1 := by
  have heq (u v : Fin n) :
      (u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ↔ u = a ∧ v = b := by
    constructor
    · rintro ⟨huv, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨rfl, rfl⟩
      · exact (lt_asymm hab huv).elim
    · rintro ⟨rfl, rfl⟩
      exact ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
  simp_rw [heq]
  simp [ite_and]

lemma single_edge_mass {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then (1 : ℝ) else 0) = 1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact single_edge_mass_of_lt a b h
  · simpa [or_comm, and_comm] using single_edge_mass_of_lt b a h

lemma tour_unordered_mass {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) :
    (∑ u : Fin n, ∑ v : Fin n, if u < v then MetricTSP.tourVec π u v else 0) = n := by
  have hexpand (u v : Fin n) :
      (if u < v then MetricTSP.tourVec π u v else 0) =
      ∑ k : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by
    rw [tourVec_eq_step_sum]
    by_cases huv : u < v <;> simp [huv]
  simp_rw [hexpand]
  calc
    _ = ∑ u : Fin n, ∑ k : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ u : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by rw [Finset.sum_comm]
    _ = ∑ _k : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      apply single_edge_mass
      intro h
      exact rotate_ne_self hn k (π.injective h).symm
    _ = n := by simp

lemma cycLen_mem_range_of_lt {n : ℕ} (u v : Fin n) (huv : u < v) :
    cycLen n u v ∈ Finset.Icc 1 (n / 2) := by
  have hu := u.isLt
  have hv := v.isLt
  have huv' : u.val < v.val := huv
  simp only [Finset.mem_Icc, cycLen,
    Int.natAbs_natCast_sub_natCast_of_le (Nat.le_of_lt huv')]
  omega

lemma sum_lenCount_eq_mass (n : ℕ) (x : Fin n → Fin n → ℝ) :
    (∑ i ∈ Finset.Icc 1 (n / 2), lenCount n i x) =
      ∑ u : Fin n, ∑ v : Fin n, if u < v then x u v else 0 := by
  unfold lenCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u < v
  · have hmem := cycLen_mem_range_of_lt u v huv
    simp [huv, hmem]
  · simp [huv]

lemma sum_lenCount_tour {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) :
    (∑ i ∈ Finset.Icc 1 (n / 2), lenCount n i (MetricTSP.tourVec π)) = n := by
  rw [sum_lenCount_eq_mass]
  exact tour_unordered_mass hn π

lemma lenCount_nonneg {n : ℕ} (π : Equiv.Perm (Fin n)) (i : ℕ) :
    0 ≤ lenCount n i (MetricTSP.tourVec π) := by
  unfold lenCount
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact tourVec_nonneg π u v
  · exact le_rfl

end CircletTSP.Facet.TourCounts

namespace CircletTSP.Facet.IdentityTour

lemma cycLen_rotate {n : ℕ} (hn : 1 < n) (u : Fin n) :
    cycLen n u (finRotate n u) = 1 := by
  cases n with
  | zero => exact Fin.elim0 u
  | succ m =>
    by_cases hu : u = Fin.last m
    · subst u
      simp [cycLen]
      omega
    · have hrot := coe_finRotate_of_ne_last hu
      have hdiff : (u.val : ℤ) - ((u.val + 1 : ℕ) : ℤ) = -1 := by omega
      simp only [cycLen, hrot, hdiff]
      norm_num
      omega

lemma cycLen_comm {n : ℕ} (u v : Fin n) : cycLen n u v = cycLen n v u := by
  have h : ((u.val : ℤ) - v.val).natAbs = ((v.val : ℤ) - u.val).natAbs := by
    rw [← Int.natAbs_neg ((u.val : ℤ) - v.val), neg_sub]
  simp only [cycLen, h]

lemma cycLen_eq_one_of_ne_zero {n : ℕ} (hn : 1 < n) (u v : Fin n)
    (h : MetricTSP.tourVec (Equiv.refl (Fin n)) u v ≠ 0) : cycLen n u v = 1 := by
  have hc : 0 < (MetricTSP.tourSteps (Equiv.refl (Fin n)) u v).card := by
    by_contra hc
    have hz := Nat.eq_zero_of_not_pos hc
    exact h (by simp [MetricTSP.tourVec, hz])
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hc
  have hi' : (i = u ∧ finRotate n i = v) ∨ (i = v ∧ finRotate n i = u) := by
    simpa [MetricTSP.tourSteps] using hi
  rcases hi' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cycLen_rotate hn i
  · rw [cycLen_comm]
    exact cycLen_rotate hn i

lemma lenCount_eq_zero {n : ℕ} (hn : 1 < n) (i : ℕ) (hi : i ≠ 1) :
    lenCount n i (MetricTSP.tourVec (Equiv.refl (Fin n))) = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  split_ifs with huv
  · by_contra hx
    exact hi (huv.2.symm.trans (cycLen_eq_one_of_ne_zero hn u v hx))
  · rfl

end CircletTSP.Facet.IdentityTour

namespace CircletTSP.Facet.IdentityTour

lemma lenCount_one {n : ℕ} (hn : 1 < n) :
    lenCount n 1 (MetricTSP.tourVec (Equiv.refl (Fin n))) = (n : ℝ) := by
  have hsum := TourCounts.sum_lenCount_tour hn (Equiv.refl (Fin n))
  rw [Finset.sum_eq_single 1] at hsum
  · exact hsum
  · intro i hi hi1
    exact lenCount_eq_zero hn i hi1
  · intro hnot
    exact (hnot (by simp only [Finset.mem_Icc]; omega)).elim

lemma circletForm_identity {n : ℕ} (hn : 1 < n) :
    circletForm n (MetricTSP.tourVec (Equiv.refl (Fin n))) = (n : ℝ) := by
  unfold circletForm
  rw [Finset.sum_eq_single 1]
  · simpa [coeff] using lenCount_one hn
  · intro i hi hi1
    rw [lenCount_eq_zero hn i hi1, mul_zero]
  · intro hnot
    exact (hnot (by simp only [Finset.mem_Icc]; omega)).elim

lemma circletForm_identity_of_four_dvd {n : ℕ} (hn : 0 < n) (h4 : 4 ∣ n) :
    circletForm n (MetricTSP.tourVec (Equiv.refl (Fin n))) = (n : ℝ) := by
  apply circletForm_identity
  have hfour : 4 ≤ n := Nat.le_of_dvd hn h4
  omega

end CircletTSP.Facet.IdentityTour

private noncomputable def circletLinear (n : ℕ) :
    (Fin n → Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := circletForm n
  map_add' x y := by
    have hif (p : Prop) [Decidable p] (a b : ℝ) :
        (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) := by
      split_ifs <;> simp
    simp only [circletForm, lenCount, Pi.add_apply, hif, Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    simp [circletForm, lenCount, Finset.mul_sum, mul_assoc, mul_comm]

private theorem equality_face_of_tight_family
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : Set E) (L : E →ₗ[ℝ] ℝ) (bound : ℝ) (m : ℕ) (hm : 0 < m)
    (hvalid : ∀ x ∈ P, bound ≤ L x)
    (hdim : Module.finrank ℝ (vectorSpan ℝ P) = m)
    (v : Fin m → E) (hmem : ∀ i, v i ∈ P) (htight : ∀ i, L (v i) = bound)
    (hind : LinearIndependent ℝ v) (p : E) (hp : p ∈ P) (hstrict : bound < L p) :
    Disjunctive.Polarity.IsFacet P (P ∩ {x | L x = bound}) := by
  let i₀ : Fin m := ⟨0, hm⟩
  have : Nonempty (Fin m) := ⟨i₀⟩
  have hF : (P ∩ {x | L x = bound}).Nonempty := ⟨v i₀, hmem i₀, htight i₀⟩
  have hP : P.Nonempty := ⟨p, hp⟩
  have hext : IsExtreme ℝ P (P ∩ {x | L x = bound}) := by
    refine ⟨Set.inter_subset_left, ?_⟩
    rintro x hx y hy z hz ⟨a, b, ha, hb, hab, hcombo⟩
    refine ⟨hx, ?_⟩
    have hvalue : a * L x + b * L y = bound := by
      calc
        a * L x + b * L y = L (a • x + b • y) := by simp
        _ = L z := congrArg L hcombo
        _ = bound := hz.2
    have habound : a * bound + b * bound = bound := by
      rw [← add_mul, hab, one_mul]
    have hax : a * (L x - bound) ≤ 0 := by
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr (hvalid y hy))]
    have hxle : L x ≤ bound := by nlinarith
    exact le_antisymm hxle (hvalid x hx)
  have hker : vectorSpan ℝ (P ∩ {x | L x = bound}) ≤ LinearMap.ker L := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, y, hy, rfl⟩
    change L (x - y) = 0
    rw [map_sub, hx.2, hy.2, sub_self]
  have hlt : vectorSpan ℝ (P ∩ {x | L x = bound}) < vectorSpan ℝ P := by
    refine lt_of_le_of_ne (vectorSpan_mono ℝ Set.inter_subset_left) ?_
    intro heq
    have hdiff : p - v i₀ ∈ vectorSpan ℝ (P ∩ {x | L x = bound}) := by
      rw [heq]
      exact vsub_mem_vectorSpan ℝ hp (hmem i₀)
    have hzero := hker hdiff
    change L (p - v i₀) = 0 at hzero
    rw [map_sub, htight] at hzero
    linarith
  have hsub : Set.range v ⊆ P ∩ {x | L x = bound} := by
    rintro _ ⟨i, rfl⟩
    exact ⟨hmem i, htight i⟩
  have hlower := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  have hfamily : Module.finrank ℝ (vectorSpan ℝ (Set.range v)) + 1 = m := by
    simpa using hind.affineIndependent.finrank_vectorSpan_add_one
  have hupper := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hdim] at hupper
  have hdimF : Module.finrank ℝ (vectorSpan ℝ (P ∩ {x | L x = bound})) + 1 = m := by
    omega
  refine ⟨hext, hF, ?_⟩
  simp only [Disjunctive.Polarity.PolyDim, if_pos hF, if_pos hP, hdim]
  omega

private theorem circlet_facet_of_strict_point (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n)
    (p : Fin n → Fin n → ℝ) (hp : p ∈ STSP n)
    (hstrict : (n : ℝ) - 2 < circletForm n p) :
    (∀ x ∈ STSP n, (n : ℝ) - 2 ≤ circletForm n x) ∧
      Disjunctive.Polarity.IsFacet (STSP n)
        (STSP n ∩ {x | circletForm n x = (n : ℝ) - 2}) := by
  have hn4 : 4 ≤ n := Nat.le_of_dvd hn h4
  have hn3 : 3 ≤ n := by omega
  have hcount : 0 < n * (n - 3) / 2 := by
    have hsub : 1 ≤ n - 3 := by omega
    have hprod : 4 ≤ n * (n - 3) := by nlinarith
    omega
  have hvalid : ∀ x ∈ STSP n, (n : ℝ) - 2 ≤ circletForm n x := by
    have hconv : Convex ℝ {x | (n : ℝ) - 2 ≤ circletLinear n x} :=
      convex_halfSpace_ge (circletLinear n).isLinear _
    apply convexHull_min _ hconv
    rintro _ ⟨π, rfl⟩
    exact theorem_3_1 n hn h4 π
  obtain ⟨τ, htight, hind⟩ := tight_tours n hn h4
  have htourmem (i : Fin (n * (n - 3) / 2)) : MetricTSP.tourVec (τ i) ∈ STSP n :=
    subset_convexHull ℝ _ ⟨τ i, rfl⟩
  have hnonempty : (STSP n).Nonempty := ⟨p, hp⟩
  have hdim : Module.finrank ℝ (vectorSpan ℝ (STSP n)) = n * (n - 3) / 2 := by
    have hd := stsp_dim n hn3
    simp only [Disjunctive.Polarity.PolyDim, if_pos hnonempty] at hd
    exact_mod_cast hd
  refine ⟨hvalid, ?_⟩
  exact equality_face_of_tight_family (STSP n) (circletLinear n) ((n : ℝ) - 2)
    (n * (n - 3) / 2) hcount hvalid hdim
    (fun i => MetricTSP.tourVec (τ i)) htourmem htight hind p hp hstrict

theorem solution (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) :
    (∀ x ∈ STSP n, (n : ℝ) - 2 ≤ circletForm n x) ∧
      Disjunctive.Polarity.IsFacet (STSP n) (STSP n ∩ {x | circletForm n x = (n : ℝ) - 2}) := by
  apply circlet_facet_of_strict_point n hn h4 (MetricTSP.tourVec (Equiv.refl (Fin n)))
  · exact subset_convexHull ℝ _ ⟨Equiv.refl (Fin n), rfl⟩
  · rw [IdentityTour.circletForm_identity_of_four_dvd hn h4]
    linarith
