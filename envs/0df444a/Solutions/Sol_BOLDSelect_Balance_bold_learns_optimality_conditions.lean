-- Prove2me | solution 1 for BOLDSelect.Balance.bold_learns_optimality_conditions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T01:05:33.429658+00:00
-- url     : https://prove2.me/submissions/613b4b52-a1fc-45db-8465-bea1e340e8ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_BOLDSelect_Balance_RateFunction
import Definitions.Def_BOLDSelect_Balance_Algorithm
import Definitions.Def_BOLDSelect_Balance_Assumptions
import Theorems.Thm_BOLDSelect_Balance_bold_total_balance
import Theorems.Thm_BOLDSelect_Balance_bold_individual_balance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BOLDSelect.Balance

theorem solution
    {M : ℕ} (hM : 2 < M) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fam : Fin M → ℝ → Measure ℝ) (hFam : ∀ x θ, IsProbabilityMeasure (Fam x θ))
    (μ : Fin M → ℝ) (hμ : Function.Injective μ)
    (xstar : Fin M) (hxstar : ∀ x, x ≠ xstar → μ x < μ xstar)
    (a b : Fin M → ℝ) (hH : ∀ x, a x < b x ∧ μ x ∈ Set.Ioo (a x) (b x))
    (Θ : Fin M → Set ℝ) (hΘ : ParameterSpace Fam μ Θ a b)
    (hA1 : Assumption1 Fam a b) (hA2 : Assumption2 Fam a b) (hA3 : Assumption3 Fam)
    (hA4 : Assumption4 Fam)
    (W : Fin M → ℕ → Ω → ℝ) (hW : ObsArray P (fun x => Fam x (μ x)) W)
    (θ0 : Fin M → ℝ) (hθ0 : ∀ x, θ0 x ∈ Θ x) (X : ℕ → Ω → Fin M)
    (hX : ∀ ω, IsBOLD Fam θ0 (fun x k => W x k ω) (fun n => X n ω)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => balanceSum Fam
        (sampleCount (fun m => X m ω) n)
        (sampleMean θ0 (fun x k => W x k ω) (fun m => X m ω) n) xstar) atTop (𝓝 1) ∧
      ∀ y z : Fin M, y ≠ xstar → z ≠ xstar →
        Tendsto (fun n =>
        gammaRate Fam (sampleCount (fun m => X m ω) n)
          (sampleMean θ0 (fun x k => W x k ω) (fun m => X m ω) n) xstar y /
        gammaRate Fam (sampleCount (fun m => X m ω) n)
          (sampleMean θ0 (fun x k => W x k ω) (fun m => X m ω) n) xstar z) atTop (𝓝 1) := by
  filter_upwards [bold_total_balance hM P Fam hFam μ hμ xstar hxstar a b hH Θ hΘ hA1 hA2 hA3 hA4
      W hW θ0 hθ0 X hX,
    bold_individual_balance hM P Fam hFam μ hμ xstar hxstar a b hH Θ hΘ hA1 hA2 hA3 hA4
      W hW θ0 hθ0 X hX] with ω h3 h4
  exact ⟨h3, h4⟩
