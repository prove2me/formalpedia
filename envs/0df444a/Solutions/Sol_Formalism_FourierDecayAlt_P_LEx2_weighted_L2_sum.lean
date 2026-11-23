-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.weighted_L2_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:12.764723+00:00
-- url     : https://prove2.me/submissions/856bdc78-f5ae-4364-9eb1-a03b666a0fce

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (B : Base) (wt : B.Ω → ℝ) (hw : ∀ ω, 0 ≤ wt ω) {I : Type} (s : Finset I) (f : I → B.Ω → ℂ)
    (hf : ∀ i ∈ s, WeightedL2 B wt (f i)) : WeightedL2 B wt (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weighted_L2_zero B wt
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact weighted_L2_add B wt hw _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end Formalism.FourierDecayAlt.P.LEx2
