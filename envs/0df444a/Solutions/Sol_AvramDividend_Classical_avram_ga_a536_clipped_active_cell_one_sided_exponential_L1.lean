-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a536_clipped_active_cell_one_sided_exponential_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:37:21.922578+00:00
-- url     : https://prove2.me/submissions/caf8502a-e118-4c0d-adfd-a8e7709c55f2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (w : ℝ → ℝ) (E Y Z : Ω → ℝ) (θ K B : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hE : ∀ᵐ ω ∂P, 0 ≤ E ω ∧ E ω ≤ 1)
    (hCell : ∀ᵐ ω ∂P, Z ω = Y ω ∨
      (-B ≤ w (Y ω) ∧ 0 < Z ω ∧
        w (Z ω) ≤ K * Real.exp (θ * Z ω)))
    (hExp : Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMeas : AEStronglyMeasurable
      (fun ω => max (E ω * (w (Z ω) - w (Y ω))) (0 : ℝ)) P) :
    Integrable (fun ω => max (E ω * (w (Z ω) - w (Y ω))) (0 : ℝ)) P := by
  have hdom : Integrable
      (fun ω => K * Real.exp (θ * Z ω) + B) P :=
    (hExp.const_mul K).add (integrable_const B)
  apply hdom.mono_nonneg hMeas
    (Filter.Eventually.of_forall fun ω => le_max_right _ _)
  filter_upwards [hE, hCell] with ω he hc
  have hge : 0 ≤ K * Real.exp (θ * Z ω) :=
    mul_nonneg hK (Real.exp_pos _).le
  have hbn : 0 ≤ K * Real.exp (θ * Z ω) + B :=
    add_nonneg hge hB
  apply max_le
  · rcases hc with hz | ⟨hy,hz,hzupper⟩
    · have hz0 : E ω * (w (Z ω) - w (Y ω)) = 0 := by simp [hz]
      rw [hz0]
      exact hbn
    · have hdiff : w (Z ω) - w (Y ω) ≤
          K * Real.exp (θ * Z ω) + B := by linarith
      have hw := mul_le_mul_of_nonneg_left hdiff he.1
      have hm := mul_le_of_le_one_left hbn he.2
      linarith
  · exact hbn
