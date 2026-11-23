-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.holder_lintegral_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:32.401834+00:00
-- url     : https://prove2.me/submissions/8b02c8fe-670e-4a81-8982-db8aed581af9

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι)
    (g : ι → Ω → ℝ≥0∞) (B : ι → ℝ≥0∞) (hg : ∀ i ∈ s, Measurable (g i))
    (h : ∀ i ∈ s, ∫⁻ ω, g i ω ^ s.card ∂μ ≤ B i ^ s.card) :
    ∫⁻ ω, ∏ i ∈ s, g i ω ∂μ ≤ ∏ i ∈ s, B i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hn : (0:ℝ) < s.card := by exact_mod_cast hs.card_pos
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := μ) s (f := fun i ω => g i ω ^ s.card)
    (fun i hi => ((hg i hi).pow_const _).aemeasurable) (p := fun _ => (1:ℝ) / s.card)
    (by simp [hn.ne']) (fun _ _ => by positivity)
  have e : ∀ x : ℝ≥0∞, (x ^ s.card) ^ ((1:ℝ) / s.card) = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hn.ne', ENNReal.rpow_one]
  simp only [e] at key
  refine key.trans (Finset.prod_le_prod' fun i hi => ?_)
  calc _ ≤ (B i ^ s.card) ^ ((1:ℝ) / s.card) := ENNReal.rpow_le_rpow (h i hi) (by positivity)
    _ = B i := e _
end Formalism.HermitianLatticeCounting.P
