-- Prove2me | solution 1 for AvramDividend.Classical.chat03_noexit_integer_horizon_integral_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:08:40.015998+00:00
-- url     : https://prove2.me/submissions/160a5eb2-55af-4eab-bb3a-76793b49e2f7

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_infinite_passage_discounted_strip_bound
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_integer_horizon_terminal_scale_vanish
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Analysis.Normed.Group.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
No-exit terminal rewards vanish also after expectation. The no-exit
event measurability is exposed as a separate obligation; all other
measurability and domination premises are discharged.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hEvent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X (a - x) ω = ∞ ∧
        twoSidedExitDownTime X (-x) ω = ∞}) :
    Tendsto
      (fun n : ℕ => ∫ ω : Ω,
        if twoSidedExitUpTime X (a - x) ω = ∞ ∧
           twoSidedExitDownTime X (-x) ω = ∞ then
          Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)
        else 0 ∂P)
      atTop (𝓝 0) := by
  let F : ℕ → Ω → ℝ := fun n ω =>
    if twoSidedExitUpTime X (a - x) ω = ∞ ∧
       twoSidedExitDownTime X (-x) ω = ∞ then
      Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)
    else 0
  have hWa : 0 ≤ W a := hW.2.1 a ha.le
  have hWmeas : Measurable W :=
    chat03_scale_function_borel_measurable X q W hW
  have hMeas : ∀ n : ℕ, AEStronglyMeasurable (F n) P := by
    intro n
    have hX : Measurable (X.X (n : ℝ≥0)) :=
      (X.adapted _).mono (𝓕.le _) le_rfl
    have hVal : Measurable (fun ω : Ω => W (x + X.X (n : ℝ≥0) ω)) :=
      hWmeas.comp (measurable_const.add hX)
    have hPay : Measurable (fun ω : Ω =>
        Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)) :=
      measurable_const.mul hVal
    exact (Measurable.ite hEvent hPay measurable_const).aestronglyMeasurable
  have hBound : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ W a := by
    intro n
    apply Filter.Eventually.of_forall
    intro ω
    by_cases he : twoSidedExitUpTime X (a - x) ω = ∞ ∧
                 twoSidedExitDownTime X (-x) ω = ∞
    · obtain ⟨hlo, hhi⟩ :=
        chat03_infinite_passage_discounted_strip_bound
          X q hq W hW a x ha hx0 hxa ω he.1 he.2 (n : ℝ≥0)
      have hVal0 : 0 ≤ F n ω := by simpa [F, he] using hlo
      have hValLe : F n ω ≤ W a := by simpa [F, he] using hhi
      simpa [Real.norm_eq_abs, abs_of_nonneg hVal0] using hValLe
    · simp [F, he, hWa]
  have hLim : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => F n ω) atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro ω
    by_cases he : twoSidedExitUpTime X (a - x) ω = ∞ ∧
                 twoSidedExitDownTime X (-x) ω = ∞
    · simpa only [F, if_pos he] using
        (chat03_noexit_integer_horizon_terminal_scale_vanish
          X q hq W hW a x ha hx0 hxa ω he.1 he.2)
    · simpa only [F, if_neg he] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun _ : Ω => W a) hMeas (integrable_const _) hBound hLim
  simpa only [F, integral_zero] using hDCT

