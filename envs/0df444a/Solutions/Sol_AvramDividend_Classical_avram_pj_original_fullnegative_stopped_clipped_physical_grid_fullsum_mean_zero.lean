-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_fullnegative_stopped_clipped_physical_grid_fullsum_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:26:55.159912+00:00
-- url     : https://prove2.me/submissions/2d1589d7-9dfc-4ee4-ba37-6939e91486db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_true_future_fullmark_past_predictable_cross_mean_zero_proved
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_complete_negative_mark_cutoff_future_count_integrable
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
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
    (∫ ω, ∑ i ∈ Finset.range m, Z i ω ∂P) = 0 := by
  intro Δ grid N r H Z
  have hStep (i : ℕ) : grid (i + 1) = grid i + Δ := by
    simp only [grid, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
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
  have hZI (i : ℕ) (hi : i ∈ Finset.range m) :
      Integrable (Z i) P := by
    have hOne :=
      avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
        X x D hD w q K hK cut ρ hρstop n m hn i
    exact hOne.integrable (by norm_num)
  have hZero (i : ℕ) (hi : i ∈ Finset.range m) :
      (∫ ω, Z i ω ∂P) = 0 := by
    have hPred :=
      avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
        G hG K hK ρ hρstop (grid i) (grid i) le_rfl
    have hNum :=
      avram_pj_original_complete_negative_mark_cutoff_future_count_integrable
        X (grid i) Δ cut
    have hMean :=
      avram_pj_original_true_future_fullmark_past_predictable_cross_mean_zero_proved
        X (grid i) Δ cut
        (fun ω => if (ρ ω : WithTop ℝ≥0) ≤
          (grid i : WithTop ℝ≥0) then 0 else H i ω)
        (by simpa only [G, Rpre, H] using hPred)
        (by simpa only [Z, N, r, hStep i, add_tsub_cancel_left] using hZI i hi)
        (by simpa only [N, r, hStep i, add_tsub_cancel_left] using hNum)
    simpa only [Z, N, r, hStep i, add_tsub_cancel_left] using hMean
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i hi
    exact hZero i hi
  · intro i hi
    exact hZI i hi
