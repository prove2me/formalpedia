-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top12_original_topcap_zero_or_preruin_closed_stieltjes_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:25:57.102307+00:00
-- url     : https://prove2.me/submissions/88644e85-dafa-416f-8041-7c9c6ba9894a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_clipped_full_stieltjes_grid_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped Topology NNReal ENNReal

/-- The exact original-process closed-cash grid budget at infinite cap, using
    the true candidate rather than a finite-cap affine extension. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτT : τ ω ≤ T)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (hzero : ∀ n, u n 0 = 0)
    (hcover : ∀ n, τ ω ≤ u n (k n))
    (mesh : ℕ → ℝ) (hm : ∀ n, 0 ≤ mesh n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ mesh n)
    (hmesh0 : Tendsto mesh atTop (𝓝 0)) :
    (let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
     (∀ n,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D 0 ω) * ENNReal.ofReal (Real.exp (-(q * 0))) +
      ((∑ i ∈ Finset.range (k n),
        ENNReal.ofReal (Real.exp (-(q * (v n (i + 1) : ℝ)))) *
          ENNReal.ofReal
            (w (x + X.X (v n (i + 1)) ω - rightLimit D (v n i) ω) -
             w (x + X.X (v n (i + 1)) ω - rightLimit D (v n (i + 1)) ω))) +
        ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ)))) ∧
     Tendsto
       (fun n => (ENNReal.ofReal (q * mesh n) *
         dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ))).toReal)
       atTop (𝓝 0)) := by
  have hVtop : C = ⊤ → ∀ z : ℝ, w z = w z := by
    intro _ _
    rfl
  have hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      w z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal) := by
    intro hne
    exact (hne hTop).elim
  exact avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_clipped_full_stieltjes_grid_budget
    X x C hC q hq w w hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω τ T hτT hPre u hu k hzero hcover mesh hm hmesh hmesh0
