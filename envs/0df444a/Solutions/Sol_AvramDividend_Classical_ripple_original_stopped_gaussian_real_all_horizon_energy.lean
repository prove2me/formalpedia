-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_stopped_gaussian_real_all_horizon_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:55:25.080309+00:00
-- url     : https://prove2.me/submissions/02a282e0-7b08-439a-93bf-213c2c090db7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval
import Theorems.Thm_AvramDividend_Classical_avram_lsc_finite_horizon_bounded_integrand_energy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (σ τ : Ω → ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
    let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
      (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
      (p.1 : WithTop ℝ≥0) ≤ τ p.2}
    ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
        (‖S.indicator G (Real.toNNReal s,ω)‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
  classical
  dsimp only
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
  let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
    (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
    (p.1 : WithTop ℝ≥0) ≤ τ p.2}
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  obtain ⟨M,hM,hderiv⟩ :=
    derivative_abs_le_on_compact_interior_interval
      w a b u v hw1 hau huv hvb
  let K : ℝ := |X.σ| * M
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg _) hM
  have hG (p : ℝ≥0 × Ω) : |G p| ≤ K := by
    dsimp [G]
    by_cases hp : Y p ∈ Icc u v
    · rw [if_pos hp, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hderiv (Y p) hp.1 hp.2) (abs_nonneg X.σ)
    · rw [if_neg hp, mul_zero, abs_zero]
      exact hK
  have hBound : ∀ ω s,
      |S.indicator G (Real.toNNReal s,ω)| ≤ K := by
    intro ω s
    by_cases hp : (Real.toNNReal s,ω) ∈ S
    · simpa only [Set.indicator_of_mem hp] using
        hG (Real.toNNReal s,ω)
    · simp only [Set.indicator_of_notMem hp, abs_zero]
      exact hK
  intro T hT
  exact avram_lsc_finite_horizon_bounded_integrand_energy
    (fun ω s => S.indicator G (Real.toNNReal s,ω))
    K hK hBound T hT
