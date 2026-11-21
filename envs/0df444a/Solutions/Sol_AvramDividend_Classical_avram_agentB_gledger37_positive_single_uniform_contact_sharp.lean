-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_gledger37_positive_single_uniform_contact_sharp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:36:19.704274+00:00
-- url     : https://prove2.me/submissions/cde17d30-72d5-42e0-b160-8485cdb6d672

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_topcap_single_clipped_cell_cash_contact_sharp_v2
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Match the actual original physical one-cell uniform mesh to the
proved positive stopped single-cell Stieltjes cash/contact bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Contact : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (w (x - rightLimit D 0 ω) - w x) +
        Finset.sum (Finset.range (m + 1)) (fun i =>
          E (v (i + 1)) *
            ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
              (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))) +
        E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) - w (Y (ρ ω))) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      q * (Δ : ℝ) * (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω - Δ : ℝ≥0) : ℝ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    ∀ᵐ ω ∂P, 0 < ρ ω → max (Contact 0 ω) (0 : ℝ) ≤ B 0 ω := by
  intro Contact B
  filter_upwards [hprefix] with ω hp hpos
  have hρn : ρ ω ≤ (n : ℝ≥0) :=
    (hρle ω).trans (by
      rw [hτeq ω]
      exact ENNReal.toNNReal_mono (by simp) (min_le_right _ _))
  have hv : min ((1 : ℝ≥0) * ((n : ℝ≥0) /
        ((0 : ℝ≥0) + 1))) (ρ ω) = ρ ω := by
    simpa using min_eq_right hρn
  have hu : ρ ω - ((n : ℝ≥0) / ((0 : ℝ≥0) + 1)) = 0 := by
    simpa using tsub_eq_zero_of_le hρn
  have hcash := avram_agentB_topcap_single_clipped_cell_cash_contact_sharp_v2
    X x C D hD w hTopCap hw0 hw_cont hw_neg hw_grad hjump
    ω (ρ ω) hpos q hq n
  have hv' : min (n : ℝ≥0) (ρ ω) = ρ ω := min_eq_right hρn
  have hu' : ρ ω - (n : ℝ≥0) = 0 := tsub_eq_zero_of_le hρn
  have hvReal : min (n : ℝ) (ρ ω : ℝ) = (ρ ω : ℝ) := by
    exact min_eq_right (by exact_mod_cast hρn)
  have hZ : x - rightLimit D 0 ω + X.X (ρ ω) ω =
      x + X.X (ρ ω) ω - rightLimit D 0 ω := by ring
  convert hcash using 1 <;>
    simp [Contact, B, hv', hvReal, hu', hZ, Finset.sum_range_succ] <;> ring
