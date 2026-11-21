-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_fullnegative_stopped_clipped_physical_grid_martingale_uniform_L2_no_extra_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:02:41.142954+00:00
-- url     : https://prove2.me/submissions/172635d8-d7ec-4a58-9af7-e9ef7a8e60cd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_clipped_stopped_negative_mark_grid_L2_energy_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_cutoff_adapted_physical_grid_exact_fullsum_L2
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_complete_negative_mark_cutoff_future_count_integrable
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_future_fullnegative_mark_grid_stopclipped_cross_weight_stronglyMeasurable
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
    (∫ ω, (∑ i ∈ Finset.range m, Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by
  intro Δ grid N r H Z
  have hStep (i : ℕ) : grid (i + 1) = grid i + Δ := by
    simp only [grid, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  have hGrid : Monotone grid := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hij) (by exact zero_le)
  have hRate (i : ℕ) : r i =
      ((Δ : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal := by
    dsimp only [r]
    rw [hStep i, add_tsub_cancel_left]
  have hVI (i : ℕ) (hi : i ∈ Finset.range m) :
      Integrable (fun ω => (N i ω).toReal - r i) P := by
    have hCell :=
      avram_pj_original_complete_negative_mark_cutoff_future_count_integrable
        X (grid i) Δ cut
    simpa only [N, r, hStep i, add_tsub_cancel_left] using hCell
  have hOne (i : ℕ) : MemLp (Z i) 2 P :=
    avram_pj_workerC_original_each_stopped_clipped_physical_marked_cell_MemLp2
      X x D hD w q K hK cut ρ hρstop n m hn i
  have hPair : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P :=
    avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
      P (Finset.range m) Z (fun i hi => hOne i)
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
  have hPast : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m, i < j →
      StronglyMeasurable[𝓕.rightCont (grid j)] (fun ω =>
        Z i ω * (if (ρ ω : WithTop ℝ≥0) ≤
          (grid j : WithTop ℝ≥0) then (0 : ℝ) else H j ω)) := by
    simpa only [G, Rpre, H] using
      (avram_pj_original_future_fullnegative_mark_grid_stopclipped_cross_weight_stronglyMeasurable
        X cut m grid hGrid N (by intro i; rfl) r
        G hG K hK ρ hρstop Z (by intro i ω; rfl))
  have hFull :=
    avram_pj_original_fullnegative_cutoff_adapted_physical_grid_exact_fullsum_L2
      X m cut Δ grid hStep N (by intro i; rfl) r hRate
      (fun i ω => if (ρ ω : WithTop ℝ≥0) ≤
        (grid i : WithTop ℝ≥0) then 0 else H i ω)
      Z (by intro i ω; rfl) hVI hPair hPast
  have hDiag :=
    avram_pj_workerC_original_clipped_stopped_negative_mark_grid_L2_energy_unconditional
      X x D hD w q K hK cut ρ hρstop n m hn
  have hSum : (∑ i ∈ Finset.range m, ∫ ω, (Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by
    rw [← integral_finset_sum]
    · exact hDiag
    · intro i hi
      simpa [pow_two] using hPair i hi i hi
  exact hFull.le.trans hSum
