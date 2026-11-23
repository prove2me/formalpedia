-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.simeq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:30.996024+00:00
-- url     : https://prove2.me/submissions/799224ff-fc78-4471-9cb6-5cf57104a125

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
open MvPowerSeries
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
theorem _root_.solution (hS : SimeqRules) {ι : Type} (s : Finset ℕ) (f : ℕ → MvPowerSeries ι K)
    (h : ∀ k ∈ s, Simeq (f k) 0) : Simeq (∑ k ∈ s, f k) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hS K ι).1 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := (hS K ι).2.2.2.1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    simpa using h1
end Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
