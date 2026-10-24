-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_capped_active_terminal_hjb_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:00:23.240206+00:00
-- url     : https://prove2.me/submissions/4b6cb5c5-11ca-4c57-a167-74fa1e6ff722

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_dividendMeasure_atom_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Up to an active positive horizon, the closed Stieltjes dividend reward is
    controlled by the strictly stopped reward and the HJB terminal jump drop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (hactive : (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ s in paymentTimes
        (min (ruinTime X x D ω) (ENNReal.ofReal (T : ℝ))),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
      (w (riskProcess X x D T ω) -
        w (riskProcess X x D T ω -
          (rightLimit D T ω - D T ω)))) := by
  let σ : ℝ≥0∞ := ruinTime X x D ω
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-(q * s)))
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hmem : (T : ℝ) ∈ paymentTimes σ := by
    refine ⟨le_of_lt hTreal, Or.inr ?_⟩
    simpa only [ENNReal.ofReal_coe_nnreal] using hactive
  have hterminal : paymentTimes σ ∩ ({(T : ℝ)} : Set ℝ) =
      ({(T : ℝ)} : Set ℝ) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · exact fun hs => hs.2
    · intro hs
      subst s
      exact ⟨hmem, rfl⟩
  have hbound :=
    local_verification_capped_dividendMeasure_atom_bound
      X x q w C hw_cont hw_smooth hw_hjb D hD hxc ω T
      (Or.inr hactive)
  change (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ), f s ∂μ) ≤
    (∫⁻ s in paymentTimes (min σ (ENNReal.ofReal (T : ℝ))),
      f s ∂μ) +
    ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
      (w (riskProcess X x D T ω) -
        w (riskProcess X x D T ω -
          (rightLimit D T ω - D T ω))))
  rw [paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom
    μ f σ (T : ℝ) hTreal]
  rw [hterminal, lintegral_singleton]
  exact add_le_add_right hbound _
