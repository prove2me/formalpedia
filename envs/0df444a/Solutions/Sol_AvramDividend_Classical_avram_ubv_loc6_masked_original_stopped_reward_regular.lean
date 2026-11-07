-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_masked_original_stopped_reward_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:46:13.346203+00:00
-- url     : https://prove2.me/submissions/dcd5b0eb-f6ec-4cb8-8d92-91d25b5ac2fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original closed-Iic reward, masked by its actual zero stopping event,
    is strongly measurable and nonnegative without a finite-mass hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P) :
    0 ≤ w x ∧
      AEStronglyMeasurable (fun ω => if σ ω = 0 then w x else F ω) P ∧
      (0 ≤ᵐ[P] fun ω => if σ ω = 0 then w x else F ω) := by
  classical
  have hValue : 0 ≤ w x :=
    avram_p3_bv_initial_value_nonnegative C hC w hw_cont hw0
      (hw_smooth.of_le (by norm_num)) hw_grad x (le_of_lt hx) hxc
  have hPay : ∀ ω, 0 ≤ F ω :=
    avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q σ F hFsource
  have hσmeas : Measurable (fun ω => (σ ω : WithTop ℝ≥0)) :=
    hσstop.measurable.mono hσstop.measurableSpace_le le_rfl
  have hZero : MeasurableSet {ω : Ω | σ ω = 0} := by
    have hPre : MeasurableSet
        ((fun ω => (σ ω : WithTop ℝ≥0)) ⁻¹' {(0 : WithTop ℝ≥0)}) :=
      hσmeas (measurableSet_singleton (0 : WithTop ℝ≥0))
    have heq : {ω : Ω | σ ω = 0} =
        ((fun ω => (σ ω : WithTop ℝ≥0)) ⁻¹' {(0 : WithTop ℝ≥0)}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact WithTop.coe_inj.symm
    rw [heq]
    exact hPre
  have hMask : AEStronglyMeasurable
      (fun ω => if σ ω = 0 then w x else F ω) P := by
    change AEStronglyMeasurable
      (Set.piecewise {ω : Ω | σ ω = 0} (fun _ => w x) F) P
    exact AEStronglyMeasurable.piecewise hZero
      aestronglyMeasurable_const.restrict hFI.aestronglyMeasurable.restrict
  refine ⟨hValue, hMask, Filter.Eventually.of_forall ?_⟩
  intro ω
  by_cases hz : σ ω = 0
  · simpa [hz] using hValue
  · simpa [hz] using hPay ω
