-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_surviving_mesh_closed_horizon_cash_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:50:23.678491+00:00
-- url     : https://prove2.me/submissions/271eb514-9d24-44bf-b2a3-2a42af6bde58

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_surviving_mesh_full_cash_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_joint_horizon_terminal_accounting

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original full-horizon stopped budget follows by absorbing the horizon
payment atom into the strict prepayment estimate on surviving sample paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (u : ℕ → ℝ≥0) (hu : StrictMono u) (n : ℕ) (hzero : u 0 = 0)
    (hFinal : u n < (⟨T, hT⟩ : ℝ≥0)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let source : ℕ → Ω → ℝ := fun i ω =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    ∀ᵐ ω ∂P, (S : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i ω) +
        e n * (V (x + X.X S ω - rightLimit D (u n) ω) -
          V (x + X.X (u n) ω - rightLimit D (u n) ω)) := by
  let S : ℝ≥0 := ⟨T, hT⟩
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
  let source : ℕ → Ω → ℝ := fun i ω =>
    V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
    V (x + X.X (u i) ω - rightLimit D (u i) ω)
  have hAtom :=
    avram_p3_bv_joint_horizon_terminal_accounting
      X x C D hD q w hjump T hT hTpos
  filter_upwards [hAtom] with ω hAtomω
  intro hSurv
  have hStrict :=
    avram_p3_bv_original_surviving_mesh_full_cash_source_budget
      X x hx C hC hxc w V hw0 hw_cont hw_neg hw_smooth
      hw_grad hVtop hVfinite D hD hjump ω q hq
      u hu n hzero S hFinal hSurv
  have hClosed :=
    (show
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) by
        simpa only [if_pos hSurv] using hAtomω)
  exact hClosed.trans hStrict
