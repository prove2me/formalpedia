-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_initial_rightjump_plus_discounted_full_stieltjes_mesh_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:42:11.294246+00:00
-- url     : https://prove2.me/submissions/44f37b6b-eff8-4519-816e-c83873d399ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_anycap_finite_mesh_discounted_endpoint_stieltjes_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact initial right-dividend jump augments every endpoint-discounted full Stieltjes mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (r : ℝ≥0),
      (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D r ω - D r ω ≤ w (riskProcess X x D r ω) -
        w (riskProcess X x D r ω - (rightLimit D r ω - D r ω)))
    (ω : Ω) (s : Finset ι) (a b : ι → ℝ≥0)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hPay : ∀ i ∈ s, (b i : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    ((rightLimit D 0 ω - D 0 ω) +
      w (riskProcess X x D 0 ω - (rightLimit D 0 ω - D 0 ω)) -
      w (riskProcess X x D 0 ω)) +
      (∑ i ∈ s, Real.exp (-(q * (b i : ℝ))) *
        ((dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))).toReal +
          V (x + X.X (b i) ω - rightLimit D (b i) ω) -
          V (x + X.X (b i) ω - rightLimit D (a i) ω))) ≤ 0 := by
  have hZero := hjump ω 0 (Or.inl rfl)
  have h0 : (rightLimit D 0 ω - D 0 ω) +
      w (riskProcess X x D 0 ω - (rightLimit D 0 ω - D 0 ω)) -
      w (riskProcess X x D 0 ω) ≤ 0 := by
    linarith only [hZero]
  have hMesh :=
    avram_p4_d_dividend_original_anycap_finite_mesh_discounted_endpoint_stieltjes_nonpositive
      X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite D hD
      ω s a b hab hPay
  exact add_nonpos h0 hMesh
