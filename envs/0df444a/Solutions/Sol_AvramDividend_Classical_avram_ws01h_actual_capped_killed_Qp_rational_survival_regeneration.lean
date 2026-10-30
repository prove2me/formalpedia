-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_capped_killed_Qp_rational_survival_regeneration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:17:40.681748+00:00
-- url     : https://prove2.me/submissions/652c5715-fc75-460e-9c4f-f8fa566aa68c

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_capped_killed_Qp_wholePath_regeneration_instantiated
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_age_fullPath_survival_reward_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The actual lower-killed capped strict upper record regenerates the
genuinely measurable countable rational-open-horizon survival reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b a : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    (let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun (u : ℝ≥0) (f : ℝ≥0 → ℝ) =>
       if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
           (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < u →
             0 ≤ a + f ((k : ℝ≥0) * (n : ℝ≥0)⁻¹))
       then (1 : ℝ≥0∞) else 0
     let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     let W : Ω → ℝ≥0∞ := fun ω => if ω ∈ A then 1 else 0
     let discount : ℝ≥0 → ℝ≥0∞ := fun u =>
       ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
     (∫⁻ z : Ω × ℝ,
       if (τ z.1 : ℝ) ≤ z.2 then
         W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
           (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
       else 0
       ∂((P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
       (∫⁻ r : ℝ, (∫⁻ ω,
         ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal r) ω -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
         ∂(expMeasure p))) := by
  classical
  let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun (u : ℝ≥0) (f : ℝ≥0 → ℝ) =>
       if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
           (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < u →
             0 ≤ a + f ((k : ℝ≥0) * (n : ℝ≥0)⁻¹))
       then (1 : ℝ≥0∞) else 0
  have hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2) :=
    avram_ws01h_rational_age_fullPath_survival_reward_measurable a
  simpa [H] using
    (avram_ws01h_actual_capped_killed_Qp_wholePath_regeneration_instantiated
      X lower b hb N θ p hθ hp H hH)
