-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_topcap_single_clipped_cell_cash_contact_sharp_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:21:50.135297+00:00
-- url     : https://prove2.me/submissions/966ff530-fc95-4889-b03f-85b8f8fb11fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
import Theorems.Thm_AvramDividend_Classical_avram_gledger133_original_stopped_mesh_terminal_contact_and_tail
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- True single original clipped cell: the zero atom and final
postpayment dividend contact cancel before bounding strict cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (ρ : ℝ≥0) (hρpos : 0 < ρ)
    (q : ℝ) (hq : 0 < q) (n : ℕ) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ := x + X.X ρ ω - rightLimit D ρ ω
    let Z : ℝ := x + X.X ρ ω - rightLimit D 0 ω
    let F : ℝ :=
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    let U : ℝ :=
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    max ((w (x - rightLimit D 0 ω) - w x) +
      E ρ * ((w (riskProcess X x D ρ ω) - w Z) +
        (w Y - w (riskProcess X x D ρ ω))) +
      E ρ * (w (riskProcess X x D ρ ω) - w Y) + F) (0 : ℝ) ≤
      q * (n : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ : ℝ))).toReal + U := by
  dsimp only
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ := x + X.X ρ ω - rightLimit D ρ ω
  let Z : ℝ := x + X.X ρ ω - rightLimit D 0 ω
  let F : ℝ :=
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let U : ℝ :=
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let v : ℕ → ℝ≥0 := fun i => if i = 0 then 0 else ρ
  have hvk : v 0 < ρ := by simpa [v] using hρpos
  have hstop : v (0 + 1) = ρ := by simp [v]
  have htail : ∀ i : ℕ, 0 < i → v i = ρ := by
    intro i hi
    simp [v, Nat.ne_of_gt hi]
  have hterm :=
    (avram_gledger133_original_stopped_mesh_terminal_contact_and_tail
      X x D hD.1.1 ω ρ v 0 hvk hstop htail
      w C hTopCap hw0 hw_cont hw_neg hw_grad q).1
  have hinitial :=
    (avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
      X x D hD.1.1 w hjump ω).1
  have hcash :=
    avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
      X x C D hD w hjump ω q (le_of_lt hq) ρ hρpos
  have hcash' : F = rightLimit D 0 ω + U := by
    simpa only [F, U] using hcash
  have hterm' :
      E ρ * (w Y - w Z) +
      E ρ * (w (riskProcess X x D ρ ω) - w Y) ≤ 0 := by
    simpa [E, Y, Z, v] using hterm
  have hmain :
      (w (x - rightLimit D 0 ω) - w x) +
      E ρ * ((w (riskProcess X x D ρ ω) - w Z) +
        (w Y - w (riskProcess X x D ρ ω))) +
      E ρ * (w (riskProcess X x D ρ ω) - w Y) + F ≤ U := by
    rw [hcash']
    have hh := hterm'
    have hz := hinitial
    nlinarith
  have hnonneg : 0 ≤ q * (n : ℝ) *
      (dividendMeasure D ω (Ioo (0 : ℝ) (ρ : ℝ))).toReal :=
    mul_nonneg (mul_nonneg (le_of_lt hq) (Nat.cast_nonneg _))
      ENNReal.toReal_nonneg
  apply max_le
  · exact hmain.trans (by linarith)
  · have hU : 0 ≤ U := ENNReal.toReal_nonneg
    linarith
