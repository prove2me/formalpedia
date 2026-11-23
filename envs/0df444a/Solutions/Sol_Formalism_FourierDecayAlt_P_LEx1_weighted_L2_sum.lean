-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.weighted_L2_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:47.450775+00:00
-- url     : https://prove2.me/submissions/5beabcbc-888a-4ee0-8446-523598c9c2f2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_weighted_L2_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_weighted_L2_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (B : Base) (wt : B.Ω → ℝ) (hw : ∀ ω, 0 ≤ wt ω) {I : Type} (s : Finset I) (f : I → B.Ω → ℂ)
    (hf : ∀ i ∈ s, WeightedL2 B wt (f i)) : WeightedL2 B wt (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using weighted_L2_zero B wt
  · intro i s hi ih hf
    have e : (fun ω => ∑ j ∈ insert i s, f j ω) = fun ω => f i ω + ∑ j ∈ s, f j ω := by
      funext ω
      rw [Finset.sum_insert hi]
    rw [e]
    exact weighted_L2_add B wt hw _ _ (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end Formalism.FourierDecayAlt.P.LEx1
