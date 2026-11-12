-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger99_original_interior_contact_cells_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:28:54.535405+00:00
-- url     : https://prove2.me/submissions/9d4d13b0-1f87-47e4-a822-9876ab0477b2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger93_original_interior_real_discounted_contact_cell
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The proved original interior dividend-contact cell bound sums over finite grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (v : ℕ → ℝ≥0) (hv : Monotone v) (k : ℕ)
    (hinterior : ∀ i : ℕ, i < k → v (i + 1) < ρ)
    (hfinite : ∀ i : ℕ, i < k →
      dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ)) ≠ ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    (Finset.sum (Finset.range k) (fun i =>
      (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
          w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤
      Finset.sum (Finset.range k) (fun i =>
        q * ((v (i + 1) : ℝ) - (v i : ℝ)) *
          (dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal) := by
  apply Finset.sum_le_sum
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  exact avram_gledger93_original_interior_real_discounted_contact_cell
    X x D hD ω ρ u hu hprefix (v i) (v (i + 1))
    (hv (Nat.le_succ i)) (hinterior i hik) q hq w C hTopCap
    hw0 hw_cont hw_neg hw_grad (hfinite i hik)
