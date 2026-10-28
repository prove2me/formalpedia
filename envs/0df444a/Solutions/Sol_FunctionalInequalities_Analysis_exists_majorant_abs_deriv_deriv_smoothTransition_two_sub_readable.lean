-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:51.144491+00:00
-- url     : https://prove2.me/submissions/36ccac1e-804e-4948-9b67-f6821c2cc77d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile
import Theorems.Thm_FunctionalInequalities_Analysis_smoothTransition_two_sub_cutoff_readable

open scoped ContDiff
/-- **A smooth majorant of `|η″|`** (Letwin Lemma A.4, p. 17, "w ≥ |η″|"): a smooth, compactly supported,
nonnegative `w`, zero off `(0, 3)`, with `|η″| ≤ w`. -/
theorem solution :
    ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧ (∀ t, 0 ≤ w t) ∧
      (∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) ∧
      ∀ t, |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ w t := by
    classical
    obtain ⟨_, _, _, _, _, houtside, _, _, ⟨B, hB, hbound⟩⟩ :=
      FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff_readable
    let w : ℝ → ℝ :=
      fun t => B * Real.smoothTransition (2 * t - 1) *
        Real.smoothTransition (5 - 2 * t)
    have hg : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (2 * t - 1)) :=
      Real.smoothTransition.contDiff.comp
        ((contDiff_const.mul contDiff_id).sub contDiff_const)
    have hh : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (5 - 2 * t)) :=
      Real.smoothTransition.contDiff.comp
        (contDiff_const.sub (contDiff_const.mul contDiff_id))
    refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [w]
      exact (contDiff_const.mul hg).mul hh
    · dsimp [w]
      apply HasCompactSupport.intro
        (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 3))
      intro t ht
      have ht' : t < 0 ∨ 3 < t := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using ht
      rcases ht' with ht' | ht'
      · have hz : Real.smoothTransition (2 * t - 1) = 0 :=
          Real.smoothTransition.zero_of_nonpos (by linarith)
        simp [hz]
      · have hz : Real.smoothTransition (5 - 2 * t) = 0 :=
          Real.smoothTransition.zero_of_nonpos (by linarith)
        simp [hz]
    · intro t
      dsimp [w]
      exact
        mul_nonneg (mul_nonneg hB (Real.smoothTransition.nonneg _))
          (Real.smoothTransition.nonneg _)
    · intro t ht
      rcases ht with ht | ht
      · have hz : Real.smoothTransition (2 * t - 1) = 0 :=
          Real.smoothTransition.zero_of_nonpos (by linarith)
        dsimp [w]
        simp [hz]
      · have hz : Real.smoothTransition (5 - 2 * t) = 0 :=
          Real.smoothTransition.zero_of_nonpos (by linarith)
        dsimp [w]
        simp [hz]
    · intro t
      have hw (x : ℝ) : 0 ≤ w x := by
        dsimp [w]
        exact
          mul_nonneg (mul_nonneg hB (Real.smoothTransition.nonneg _))
            (Real.smoothTransition.nonneg _)
      by_cases ht : t ∈ Set.Icc (1 : ℝ) 2
      · have h₁ : Real.smoothTransition (2 * t - 1) = 1 :=
          Real.smoothTransition.one_of_one_le (by linarith [ht.1])
        have h₂ : Real.smoothTransition (5 - 2 * t) = 1 :=
          Real.smoothTransition.one_of_one_le (by linarith [ht.2])
        have hw_eq : w t = B := by
          simp [w, h₁, h₂]
        rw [hw_eq]
        exact (hbound t).2
      · have hout : t < 1 ∨ 2 < t := by
          simpa only [Set.mem_Icc, not_and_or, not_le] using ht
        have hzero := houtside t hout
        rw [hzero.2, abs_zero]
        exact hw t
