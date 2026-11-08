-- Prove2me | solution 1 for BartlettBousquetMendelson.LocalRad.proof_thm_3_3_p16_subroot_growth
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:47:17.564208+00:00
-- url     : https://prove2.me/submissions/08df2951-c11f-4cda-8f62-d7a59382df47

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsSubRoot

open BartlettBousquetMendelson.LocalRad in
theorem solution (ψ : ℝ → ℝ) (hψ : IsSubRoot ψ) :
    (∀ r β : ℝ, 0 ≤ r → 1 ≤ β → ψ (β * r) ≤ Real.sqrt β * ψ r) ∧
      ∀ rstar : ℝ, 0 < rstar → ψ rstar = rstar →
        ∀ r : ℝ, rstar ≤ r → ψ r ≤ Real.sqrt (r * rstar) := by
  obtain ⟨hnn, -, hanti⟩ := hψ
  refine ⟨fun r β hr hβ => ?_, fun rstar hrs hfix r hr => ?_⟩
  · have hsβ : 1 ≤ Real.sqrt β := by rw [Real.one_le_sqrt]; exact hβ
    rcases hr.lt_or_eq with hr' | hr'
    · have hβr : r ≤ β * r := le_mul_of_one_le_left hr hβ
      have hβr0 : 0 < β * r := lt_of_lt_of_le hr' hβr
      have h := hanti (Set.mem_Ioi.mpr hr') (Set.mem_Ioi.mpr hβr0) hβr
      simp only at h
      have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr'
      rw [Real.sqrt_mul (by linarith) r, div_le_div_iff₀ (mul_pos (by linarith) hsr) hsr] at h
      have h' : ψ (β * r) * Real.sqrt r ≤ (Real.sqrt β * ψ r) * Real.sqrt r := by linarith
      exact le_of_mul_le_mul_right h' hsr
    · subst hr'
      rw [mul_zero]
      exact le_mul_of_one_le_left (hnn 0 le_rfl) hsβ
  · have hr0 : 0 < r := lt_of_lt_of_le hrs hr
    have h := hanti (Set.mem_Ioi.mpr hrs) (Set.mem_Ioi.mpr hr0) hr
    simp only at h
    rw [hfix, Real.div_sqrt, div_le_iff₀ (Real.sqrt_pos.mpr hr0)] at h
    rw [Real.sqrt_mul hr0.le]
    linarith
