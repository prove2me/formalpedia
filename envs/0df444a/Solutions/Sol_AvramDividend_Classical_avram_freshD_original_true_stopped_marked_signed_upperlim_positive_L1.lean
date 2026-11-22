-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_true_stopped_marked_signed_upperlim_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:37:57.142309+00:00
-- url     : https://prove2.me/submissions/ec7aa19c-8434-4b03-be64-a7d4c8080428

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (marked : ℕ → Ω → Finset ℕ)
    (hmarked : ∀ m ω, marked m ω =
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let grid : ℕ → ℝ≥0 := fun i =>
        min ((i : ℝ≥0) * Δ) (σ ω)
      (by
        classical
        exact (Finset.range (m + 1)).filter (fun i =>
          ∃ u : ℝ≥0, grid i < u ∧ u ≤ grid (i + 1) ∧
            X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)))
    (W : ℕ → Ω → ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hW : ∀ m i ω, |W m ω i| ≤ L)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => max (∑ i ∈ marked m ω, W m ω i) 0) P)
    (hUpper : ∀ᵐ ω ∂P, Tendsto
      (fun m => max (∑ i ∈ marked m ω, W m ω i) 0)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun m => ∫ ω, max (∑ i ∈ marked m ω, W m ω i) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t,
        X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
  let N : Ω → ℝ := fun ω =>
    ((NX ω) (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal
  have hNI : Integrable N P := by
    simpa only [NX, N] using
      avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
        X hFinite n
  have hCount (m : ℕ) : ∀ᵐ ω ∂P,
      ((marked m ω).card : ℝ) ≤ N ω := by
    have hm :=
      avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
        X hFinite n m σ hσstop hσbound
    rcases hm with ⟨_, _, hb⟩
    filter_upwards [hb] with ω hω
    simpa only [hmarked m ω, NX, N] using hω
  have hDom (m : ℕ) : ∀ᵐ ω ∂P,
      ‖max (∑ i ∈ marked m ω, W m ω i) 0‖ ≤ L * N ω := by
    filter_upwards [hCount m] with ω hc
    have hsum : |∑ i ∈ marked m ω, W m ω i| ≤
        L * N ω := by
      calc
        _ ≤ ∑ i ∈ marked m ω, |W m ω i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ marked m ω, L := by
          apply Finset.sum_le_sum
          intro i hi
          exact hW m i ω
        _ = L * ((marked m ω).card : ℝ) := by
          simp [mul_comm]
        _ ≤ L * N ω := mul_le_mul_of_nonneg_left hc hL
    have hn : 0 ≤ L * N ω := by
      apply mul_nonneg hL
      exact le_trans (Nat.cast_nonneg _) hc
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_trans (le_abs_self _) hsum) hn
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun ω => L * N ω) hMeas (hNI.const_mul L) hDom hUpper
  simpa only [integral_zero] using hDCT
