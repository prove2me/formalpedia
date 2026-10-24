-- Prove2me | solution 1 for AvramDividend.Classical.causal_cutoff_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:57:07.72724+00:00
-- url     : https://prove2.me/submissions/9a2df130-cbc2-40ce-a4d7-fab44d05edaa

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology

/-- Split a causal L1 kernel into a bounded continuous tail and a
remainder supported close to zero. -/
theorem solution
    (f : ℝ → ℝ) (hfint : Integrable f volume)
    (hfcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hfbound : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |f x| ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F U : ℝ → ℝ, (∀ t, f t = F t + U t) ∧ Continuous F ∧
      BddAbove (range fun t : ℝ => ‖F t‖) ∧ Integrable U volume ∧
      (∀ t, 2 * ε < t → U t = 0) := by
  let χ : ℝ → ℝ := fun t => max 0 (min 1 ((t - ε) / ε))
  obtain ⟨hχc, hχzero, hχone⟩ :=
    positive_ramp_cutoff_continuous_and_support ε hε
  have hχ0 (t : ℝ) : 0 ≤ χ t := le_max_left _ _
  have hχ1 (t : ℝ) : χ t ≤ 1 := by
    dsimp [χ]; exact max_le (by norm_num) (min_le_left _ _)
  have hχabs (t : ℝ) : |χ t| ≤ 1 := by
    rw [abs_of_nonneg (hχ0 t)]; exact hχ1 t
  have hηabs (t : ℝ) : |1 - χ t| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hχ1 t))]; linarith [hχ0 t]
  let F : ℝ → ℝ := fun t => χ t * f t
  let U : ℝ → ℝ := fun t => (1 - χ t) * f t
  have hFc : Continuous F := by
    rw [continuous_iff_continuousAt]; intro t
    by_cases ht : t < ε
    · have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] F := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with y hy
        have hcut : χ y = 0 := hχzero y (le_of_lt hy)
        simp only [F, hcut, zero_mul]
      exact continuousAt_const.congr_of_eventuallyEq heq.symm
    · have htpos : 0 < t := by linarith
      exact hχc.continuousAt.mul (hfcont.continuousAt (isOpen_Ioi.mem_nhds htpos))
  obtain ⟨M, hM⟩ := hfbound ε hε
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f ε)) (hM ε le_rfl)
  have hFb : BddAbove (range fun t : ℝ => ‖F t‖) := by
    refine ⟨M, ?_⟩; rintro z ⟨t, rfl⟩
    by_cases ht : t ≤ ε
    · change ‖χ t * f t‖ ≤ M
      rw [show χ t = 0 from hχzero t ht]
      simpa using hM0
    · have hp : |χ t * f t| ≤ |f t| := by
        calc
          |χ t * f t| = |χ t| * |f t| := abs_mul _ _
          _ ≤ 1 * |f t| :=
            mul_le_mul_of_nonneg_right (hχabs t) (abs_nonneg _)
          _ = |f t| := one_mul _
      exact (by simpa [F, Real.norm_eq_abs] using
        le_trans hp (hM t (le_of_lt (lt_of_not_ge ht))))
  have hUi : Integrable U volume := by
    have hc : Continuous (fun t : ℝ => 1 - χ t) := continuous_const.sub hχc
    have hb : ∀ᵐ t : ℝ ∂volume, ‖1 - χ t‖ ≤ (1 : ℝ) :=
      Filter.Eventually.of_forall (fun t => by simpa [Real.norm_eq_abs] using hηabs t)
    simpa [U] using (hfint.bdd_mul hc.aestronglyMeasurable hb)
  refine ⟨F, U, ?_, hFc, hFb, hUi, ?_⟩
  · intro t; dsimp [F, U]; ring
  · intro t ht; dsimp [U]
    have hunit : χ t = 1 := hχone t (le_of_lt ht)
    rw [hunit]; ring
