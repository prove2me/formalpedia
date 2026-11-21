-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_future_fullnegative_mark_grid_stopclipped_cross_weight_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:44:16.871458+00:00
-- url     : https://prove2.me/submissions/8e18d655-0fe2-4cc4-9bc2-98feef4b10bc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The earlier original stopped clipped negative-mark compensated
increment multiplied by any later stopped predictable weight is
measurable in the true later right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (cut m : ℕ) (grid : ℕ → ℝ≥0)
    (hGrid : Monotone grid)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ
          Iic (-(1 / ((cut : ℝ) + 1)))))
    (r : ℕ → ℝ)
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : IsStronglyPredictable 𝓕.rightCont Y)
    (K : ℝ) (hK : 0 ≤ K)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ω, Z i ω =
      (if (ρ ω : WithTop ℝ≥0) ≤
        (grid i : WithTop ℝ≥0) then (0 : ℝ)
      else max (-K) (min K (Y (grid i) ω))) *
        ((N i ω).toReal - r i)) :
    ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m, i < j →
      StronglyMeasurable[𝓕.rightCont (grid j)] (fun ω =>
        Z i ω * (if (ρ ω : WithTop ℝ≥0) ≤
          (grid j : WithTop ℝ≥0) then (0 : ℝ)
        else max (-K) (min K (Y (grid j) ω)))) := by
  intro i hi j hj hij
  have hCoeffI :=
    avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
      Y hY K hK ρ hρstop (grid i) (grid j)
        (hGrid (Nat.le_of_lt hij))
  have hCoeffJ :=
    avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
      Y hY K hK ρ hρstop (grid j) (grid j) le_rfl
  have hNraw :=
    avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
      X (grid i) (grid (i + 1)) (grid j)
      (hGrid (Nat.succ_le_of_lt hij))
      (Iic (-(1 / ((cut : ℝ) + 1)))) measurableSet_Iic
  have hN : StronglyMeasurable[𝓕.rightCont (grid j)]
      (fun ω => (N i ω).toReal) := by
    simpa only [hActual i] using hNraw
  have hZi : StronglyMeasurable[𝓕.rightCont (grid j)] (Z i) := by
    have hSM := hCoeffI.mul
      (hN.sub (stronglyMeasurable_const :
        StronglyMeasurable[𝓕.rightCont (grid j)]
          (fun _ : Ω => r i)))
    convert hSM using 1
    funext ω
    exact hZ i ω
  exact hZi.mul hCoeffJ
