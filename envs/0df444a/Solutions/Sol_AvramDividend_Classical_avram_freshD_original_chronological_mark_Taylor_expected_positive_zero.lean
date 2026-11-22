-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_chronological_mark_Taylor_expected_positive_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T14:21:45.653334+00:00
-- url     : https://prove2.me/submissions/a634ad86-b976-4da7-8887-801635d4bfbf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_finite_mark_times_grid_prestates_Taylor_upperlim
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (c : ℝ)
    (hc : 0 < c) (hcC : ENNReal.ofReal c ≤ C)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (n : ℕ) (S : Ω → Finset ℝ≥0)
    (hSpos : ∀ ω t, t ∈ S ω → 0 < t)
    (hSneg : ∀ ω t, t ∈ S ω →
      X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0)
    (hSinterior : ∀ ω t, t ∈ S ω →
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω ∈
        Ioo (0 : ℝ) c)
    (hCount : ∀ᵐ ω ∂P, ((S ω).card : ℝ) ≤
      (((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t,
            X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
          (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal)
    (grid : ℕ → Ω → ℝ≥0 → ℝ≥0)
    (hgrid : ∀ᵐ ω ∂P, ∀ t ∈ S ω,
      Tendsto (fun m => grid m ω t) atTop (𝓝[<] t))
    (E : ℕ → Ω → ℝ≥0 → ℝ)
    (hEsource : ∀ m ω t,
      E m ω t =
        let y := x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t -
          D t ω
        let z := X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
        let u := x + X.X (grid m ω t) ω -
          rightLimit D (grid m ω t) ω
        ((w (u + z) - w u -
          (if -1 < z then z * deriv w u else 0)) -
         (w (y + z) - w y -
          (if -1 < z then z * deriv w y else 0))))
    (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ m ω t, t ∈ S ω → |E m ω t| ≤ L)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => max (∑ t ∈ S ω, E m ω t) 0) P) :
    Tendsto
      (fun m => ∫ ω, max (∑ t ∈ S ω, E m ω t) 0 ∂P)
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
  have hCountN : ∀ᵐ ω ∂P, ((S ω).card : ℝ) ≤ N ω := by
    simpa only [NX, N] using hCount
  have hDom (m : ℕ) : ∀ᵐ ω ∂P,
      ‖max (∑ t ∈ S ω, E m ω t) 0‖ ≤ L * N ω := by
    filter_upwards [hCountN] with ω hcω
    have hsum : |∑ t ∈ S ω, E m ω t| ≤ L * N ω := by
      calc
        _ ≤ ∑ t ∈ S ω, |E m ω t| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _t ∈ S ω, L := by
          apply Finset.sum_le_sum
          intro t ht
          exact hBound m ω t ht
        _ = L * ((S ω).card : ℝ) := by simp [mul_comm]
        _ ≤ L * N ω := mul_le_mul_of_nonneg_left hcω hL
    have hn : 0 ≤ L * N ω :=
      mul_nonneg hL (le_trans (Nat.cast_nonneg _) hcω)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_trans (le_abs_self _) hsum) hn
  have hPoint : ∀ᵐ ω ∂P,
      Tendsto (fun m => max (∑ t ∈ S ω, E m ω t) 0)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hgrid] with ω hgridω
    have hMarked :=
      avram_freshD_original_true_finite_mark_times_grid_prestates_Taylor_upperlim
        X x D hD ω w C c hc hcC hw_smooth hw0 hwcont hwneg
        (S ω) (hSpos ω) (hSneg ω) (hSinterior ω)
        (fun m t => grid m ω t) hgridω
    simpa only [hEsource] using hMarked
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun ω => L * N ω) hMeas (hNI.const_mul L) hDom hPoint
  simpa only [integral_zero] using hDCT
