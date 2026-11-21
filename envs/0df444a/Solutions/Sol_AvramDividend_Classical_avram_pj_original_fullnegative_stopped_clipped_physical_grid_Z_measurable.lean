-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_fullnegative_stopped_clipped_physical_grid_Z_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:16:53.305374+00:00
-- url     : https://prove2.me/submissions/eff8472a-e25e-4909-b184-efafde37e84d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hn : 0 < n) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    ∀ i : ℕ, Measurable (Z i) := by
  intro Δ grid N r H Z i
  have hStep (j : ℕ) : grid (j + 1) = grid j + Δ := by
    simp only [grid, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  have hle : grid i ≤ grid (i + 1) := by
    rw [hStep i]
    exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ Δ)
  let Rpre : ℝ≥0 → Ω → ℝ := fun t ω =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(q * (t : ℝ))) * deriv w (Rpre t ω)
  have hRpre : IsStronglyPredictable 𝓕.rightCont Rpre := by
    simpa only [Rpre] using
      (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD)
  have hG : IsStronglyPredictable 𝓕.rightCont G := by
    simpa only [G] using
      (avram_wave3_04_discounted_deriv_stronglyPredictable Rpre hRpre w q)
  have hHM : Measurable (fun ω =>
      if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
      then (0 : ℝ) else H i ω) := by
    have hStrong :=
      avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
        G hG K hK ρ hρstop (grid i) (grid (i + 1)) hle
    have hM := (hStrong.mono (𝓕.rightCont.le (grid (i + 1)))).measurable
    simpa only [H, G, Rpre] using hM
  have hNM : Measurable (fun ω => (N i ω).toReal) := by
    have hStrong :=
      avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
        X (grid i) (grid (i + 1)) (grid (i + 1)) le_rfl
        (Iic (-(1 / ((cut : ℝ) + 1)))) measurableSet_Iic
    have hM := (hStrong.mono (𝓕.rightCont.le (grid (i + 1)))).measurable
    simpa only [N] using hM
  dsimp only [Z]
  exact hHM.mul (hNM.sub measurable_const)
