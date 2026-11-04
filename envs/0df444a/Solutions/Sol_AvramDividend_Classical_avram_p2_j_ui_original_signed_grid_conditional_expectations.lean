-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_signed_grid_conditional_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:05:50.322078+00:00
-- url     : https://prove2.me/submissions/26f632a0-3319-429b-92da-89ba2389fdb1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_grid_l2_conditional_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_finite_sum_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Fully signed original Lévy grid application with explicit pointwise and a.e. assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hg : ∀ y, ‖g y‖ₑ ≤ f y)
    (h : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n ω, Y n ω = ∑ i ∈ Finset.range n,
      g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
        X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
    (hmesh : Tendsto h atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hhor : ∀ᶠ n : ℕ in atTop, (n : ℝ) * h n ≤ T)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  apply avram_p2_j_ui_original_grid_l2_conditional_expectations
    P X ε hε T hT f M hM hf h Y Z hmesh hhor hm
  · intro n
    exact Eventually.of_forall (fun ω => by
      rw [hY n ω]
      exact avram_p2_j_ui_signed_finite_sum_envelope
        (Finset.range n)
        (fun i => g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
          X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
        (fun i => f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
          X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
        (fun i hi => hg _))
  · exact hae
