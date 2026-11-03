-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_signed_stieltjes_integrable_iff_expected_cash_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:53:59.106588+00:00
-- url     : https://prove2.me/submissions/53bcc36a-47d9-4b26-8ed0-c1930a566ce6

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The genuine source signed Stieltjes payout is L1 at an arbitrary
    finite measurable random clock iff the full expected ENNReal cash is finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) ↔
    ((∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≠ ⊤) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hMeas : Measurable F := by
    exact avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hDiv q (fun ω => (τ ω : ℝ)) hτMeas
  have hPath (ω : Ω) : F ω = ENNReal.ofReal (g ω) := by
    exact avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
      X x D hDiv ω (τ ω : ℝ) (NNReal.coe_nonneg _) q hq
  have hg (ω : Ω) : 0 ≤ g ω := by
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hEq : (fun ω => (F ω).toReal) =ᵐ[P] g := by
    apply Filter.Eventually.of_forall
    intro ω
    calc
      (F ω).toReal = (ENNReal.ofReal (g ω)).toReal :=
        congrArg ENNReal.toReal (hPath ω)
      _ = g ω := ENNReal.toReal_ofReal (hg ω)
  have hFne (ω : Ω) : F ω ≠ ⊤ := by
    rw [hPath ω]
    exact ENNReal.ofReal_ne_top
  have hAeMeas : AEMeasurable F P := hMeas.aemeasurable
  have hFneAE : ∀ᵐ ω ∂P, F ω ≠ ⊤ :=
    Filter.Eventually.of_forall hFne
  have hIff :
      (Integrable (fun ω => (F ω).toReal) P ↔
        (∫⁻ ω, F ω ∂P) ≠ ⊤) :=
    MeasureTheory.integrable_toReal_iff hAeMeas hFneAE
  change Integrable g P ↔ (∫⁻ ω, F ω ∂P) ≠ ⊤
  constructor
  · intro hG
    exact hIff.mp (hG.congr hEq.symm)
  · intro hFinite
    exact (hIff.mpr hFinite).congr hEq
