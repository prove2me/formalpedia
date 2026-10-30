-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_markov_tonelli_killed_history_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:11:52.135087+00:00
-- url     : https://prove2.me/submissions/43159b0c-1b0e-4f09-9cad-6a579ac885ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Genuine source-Lévy Markov–Tonelli factorisation for a historical
reserve/survival flag and continuously monitored (on a complete rational
schedule) future killed nonnegative payoff. No PRM or independence premise
is assumed beyond the original Lévy process axioms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ × Bool) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T : ℝ≥0) (q : ℝ)
    (W : ℝ → ℝ) (hW : Measurable W) :
    (∫⁻ ω,
      (if (H ω).2 then
        if ∀ j : ℕ, τ j ≤ T →
            0 ≤ (H ω).1 + (X.X (s + τ j) ω - X.X s ω) then
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
            W ((H ω).1 + (X.X (s + T) ω - X.X s ω)))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞)) ∂P) =
    ∫⁻ h, ∫⁻ y,
      (if h.2 then
        if ∀ j : ℕ, τ j ≤ T → 0 ≤ h.1 + y (τ j) then
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (h.1 + y T))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)
      ∂(Measure.map H P) := by
  classical
  let F : (ℝ × Bool) × (ℝ≥0 → ℝ) → ℝ≥0∞ := fun z =>
    if z.1.2 then
      if ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1.1 + z.2 (τ j) then
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
          W (z.1.1 + z.2 T))
      else 0
    else 0
  have hReserve : Measurable (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hPath : Measurable (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => z.2) :=
    measurable_snd
  have hPair : Measurable (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => (z.1.1, z.2)) :=
    hReserve.prodMk hPath
  have hEvent : MeasurableSet
      {z : (ℝ × Bool) × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1.1 + z.2 (τ j)} := by
    simpa only [preimage, mem_setOf_eq] using
      (chat04_countable_shifted_future_reserve_survival_measurable τ T).preimage hPair
  have hBool : Measurable (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hFlag : MeasurableSet
      {z : (ℝ × Bool) × (ℝ≥0 → ℝ) | z.1.2 = true} :=
    hBool (measurableSet_singleton true)
  have hTerm : Measurable
      (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) => z.1.1 + z.2 T) :=
    hReserve.add ((measurable_pi_apply T).comp hPath)
  have hPay : Measurable
      (fun z : (ℝ × Bool) × (ℝ≥0 → ℝ) =>
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
          W (z.1.1 + z.2 T))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hW.comp hTerm))
  have hF : Measurable F :=
    Measurable.ite hFlag (Measurable.ite hEvent hPay measurable_const) measurable_const
  simpa only [F] using
    (chat04_unconditional_history_future_path_markov_tonelli X s H hH F hF)
