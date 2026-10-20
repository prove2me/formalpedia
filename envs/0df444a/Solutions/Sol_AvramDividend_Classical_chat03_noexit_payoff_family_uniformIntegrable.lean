-- Prove2me | solution 1 for AvramDividend.Classical.chat03_noexit_payoff_family_uniformIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:40:32.572993+00:00
-- url     : https://prove2.me/submissions/2df3194c-adff-41c8-8e06-f25540ba3468

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_infinite_passage_discounted_strip_bound
import Theorems.Thm_AvramDividend_Classical_chat03_uniformIntegrable_of_pointwise_bounded_family
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Conditionally measurable payoff family, truncated onto the sample paths
where both official strict passage clocks are infinite. The accepted
strip bound makes this family uniformly integrable in L1.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (f : ℝ≥0 → Ω → ℝ)
    (hf : ∀ t ω, f t ω =
      if twoSidedExitUpTime X (a - x) ω = ∞ ∧
         twoSidedExitDownTime X (-x) ω = ∞ then
        Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
      else 0)
    (hmeas : ∀ t, AEStronglyMeasurable (f t) P) :
    UniformIntegrable f (1 : ℝ≥0∞) P := by
  have hWa : 0 ≤ W a := hW.2.1 a ha.le
  apply chat03_uniformIntegrable_of_pointwise_bounded_family
    f hmeas (‖W a‖₊)
  intro t ω
  rw [hf t ω]
  split_ifs with hboth
  · obtain ⟨hu, hd⟩ := hboth
    obtain ⟨hv0, hvle⟩ :=
      chat03_infinite_passage_discounted_strip_bound
        X q hq W hW a x ha hx0 hxa ω hu hd t
    rw [Real.nnnorm_of_nonneg hv0, Real.nnnorm_of_nonneg hWa]
    exact_mod_cast hvle
  · simp
