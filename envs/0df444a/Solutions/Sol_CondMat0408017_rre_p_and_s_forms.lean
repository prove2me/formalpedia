-- Prove2me | solution 1 for CondMat0408017.rre_p_and_s_forms
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:27:11.750807+00:00
-- url     : https://prove2.me/submissions/6231fc53-dc03-4337-a271-23cdb57eabd4

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (eps : ℂ) (wv : ℝ) (α α0 : ℝ → ℂ)
    (hα : ∀ q, α q ^ 2 = eps * wv ^ 2 - q ^ 2) (hα0 : ∀ q, α0 q ^ 2 = wv ^ 2 - q ^ 2)
    (I0 : ℂ → ℝ → ℂ) :
    (∀ sgn : ℂ, (sgn = 1 ∨ sgn = -1) → ∀ p q : ℝ, α p - sgn * α0 q ≠ 0 →
      rreM eps sgn p q (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q) =
          (eps - 1) * (rreNp sgn p q (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q)) ∧
        rreM 1 sgn p q (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q) =
          (eps - 1) * (wv : ℂ) ^ 2 * (rreNs sgn (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q))) ∧
    (∀ (R : DKernel) (p k : ℝ), eps ≠ 1 → α p - α0 k ≠ 0 → α p + α0 k ≠ 0 →
      (DKernel.applyLeft
            (fun p q => rreM eps 1 p q (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
          rreM eps (-1) p k (α p) (α0 k) * I0 (α p + α0 k) (p - k) ↔
        DKernel.applyLeft
            (fun p q => rreNp 1 p q (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
          rreNp (-1) p k (α p) (α0 k) * I0 (α p + α0 k) (p - k)) ∧
      (wv ≠ 0 →
        (DKernel.applyLeft
              (fun p q => rreM 1 1 p q (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
            rreM 1 (-1) p k (α p) (α0 k) * I0 (α p + α0 k) (p - k) ↔
          DKernel.applyLeft
              (fun p q => rreNs 1 (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
            rreNs (-1) (α p) (α0 k) * I0 (α p + α0 k) (p - k)))) := by
  have hpart1 : ∀ sgn : ℂ, (sgn = 1 ∨ sgn = -1) → ∀ p q : ℝ, α p - sgn * α0 q ≠ 0 →
      rreM eps sgn p q (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q) =
          (eps - 1) * (rreNp sgn p q (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q)) ∧
        rreM 1 sgn p q (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q) =
          (eps - 1) * (wv : ℂ) ^ 2 * (rreNs sgn (α p) (α0 q) * I0 (α p - sgn * α0 q) (p - q)) := by
    intro sgn hsgn p q hne
    have hsgn2 : sgn ^ 2 = 1 := by rcases hsgn with rfl | rfl <;> norm_num
    have hαp := hα p
    have hα0q := hα0 q
    constructor
    · have hM_eq : rreM eps sgn p q (α p) (α0 q) = (eps - 1) * rreNp sgn p q (α p) (α0 q) := by
        simp only [rreM, rreNp]
        rcases hsgn with rfl | rfl <;>
          simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hne ⊢ <;>
          field_simp [hne]
        · linear_combination hαp - eps * hα0q
        · linear_combination -hαp + eps * hα0q
      rw [hM_eq, mul_assoc]
    · have hM_eq : rreM 1 sgn p q (α p) (α0 q) =
          (eps - 1) * (wv : ℂ) ^ 2 * rreNs sgn (α p) (α0 q) := by
        simp only [rreM, rreNs]
        rcases hsgn with rfl | rfl <;>
          simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hne ⊢ <;>
          field_simp [hne]
        · linear_combination hαp - hα0q
        · linear_combination -hαp + hα0q
      rw [hM_eq, mul_assoc]
  refine ⟨hpart1, ?_⟩
  intro R p k heps hne1 hne2
  have hae : ∀ᵐ q : ℝ, α p - α0 q ≠ 0 := by
    have hfin : Set.Finite {q : ℝ | α p - α0 q = 0} := by
      by_cases hne : ({q : ℝ | α p - α0 q = 0} : Set ℝ).Nonempty
      · obtain ⟨q0, hq0⟩ := hne
        refine Set.Finite.subset (Set.finite_singleton q0 |>.union (Set.finite_singleton (-q0))) ?_
        intro q hq
        have hq' : α0 q = α p := (sub_eq_zero.mp hq).symm
        have hq0' : α0 q0 = α p := (sub_eq_zero.mp hq0).symm
        have hsqC : (q : ℂ) ^ 2 = (q0 : ℂ) ^ 2 := by
          have h1 := hα0 q
          have h2 := hα0 q0
          rw [hq'] at h1; rw [hq0'] at h2
          linear_combination h1 - h2
        have hsqR : q ^ 2 = q0 ^ 2 := by
          apply Complex.ofReal_injective
          push_cast
          exact hsqC
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqR with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]
        exact Set.finite_empty
    rw [ae_iff]
    simpa [not_not] using hfin.measure_zero volume
  have heps_ne : eps - 1 ≠ 0 := sub_ne_zero.mpr heps
  have h1m := hpart1 (-1) (Or.inr rfl) p k (by simpa using hne2)
  have h1p := hpart1 1 (Or.inl rfl) p k (by simpa using hne1)
  simp only [one_mul, neg_one_mul, sub_neg_eq_add] at h1m h1p
  constructor
  · have hleft : DKernel.applyLeft
        (fun p q => rreM eps 1 p q (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
        (eps - 1) * DKernel.applyLeft
          (fun p q => rreNp 1 p q (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k := by
      simp only [DKernel.applyLeft, mul_add]
      congr 1
      · rw [h1p.1]; ring
      · rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hae] with q hq
        have hq' := (hpart1 1 (Or.inl rfl) p q (by simpa using hq)).1
        simp only [one_mul] at hq'
        rw [hq']
        ring
    rw [hleft, h1m.1]
    exact mul_right_inj' heps_ne
  · intro hwv
    have hfac_ne : (eps - 1) * (wv : ℂ) ^ 2 ≠ 0 :=
      mul_ne_zero heps_ne (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hwv))
    have hleft : DKernel.applyLeft
        (fun p q => rreM 1 1 p q (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k =
        (eps - 1) * (wv : ℂ) ^ 2 * DKernel.applyLeft
          (fun p q => rreNs 1 (α p) (α0 q) * I0 (α p - α0 q) (p - q)) R p k := by
      simp only [DKernel.applyLeft, mul_add]
      congr 1
      · rw [h1p.2]; ring
      · rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hae] with q hq
        have hq' := (hpart1 1 (Or.inl rfl) p q (by simpa using hq)).2
        simp only [one_mul] at hq'
        rw [hq']
        ring
    rw [hleft, h1m.2]
    exact mul_right_inj' hfac_ne
