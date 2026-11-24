-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.vlet_prod_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:19.197137+00:00
-- url     : https://prove2.me/submissions/aee2f8ba-881f-4f50-85ac-a407654356fc

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_ins_lift0_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (sites : List (Site A)) (l : Letter K S) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((sites.map fun σ => (vlet σ l : SlopeTestRemainingChoices S A)).prod * B) x y =
      ∑ j, (sites.map (lm l)).prod (x l.intersection_update_fsHerm_neg_one) j * B (Function.update x l.intersection_update_fsHerm_neg_one j) y := by
  induction sites generalizing x with
  | nil => simp [Matrix.one_apply]
  | cons σ sites ih =>
    have hu : ∀ j : Fin 2, Function.update x l.intersection_update_fsHerm_neg_one j l.intersection_update_fsHerm_neg_one = j := fun j => by simp
    have hu2 : ∀ j j' : Fin 2, Function.update (Function.update x l.intersection_update_fsHerm_neg_one j) l.intersection_update_fsHerm_neg_one j' =
        Function.update x l.intersection_update_fsHerm_neg_one j' := fun j j' => by simp
    have hv : (vlet σ l : SlopeTestRemainingChoices S A) = ins l.intersection_update_fsHerm_neg_one (lift0 (lm l σ)) := rfl
    simp only [List.map_cons, List.prod_cons, mul_assoc]
    rw [hv, ins_lift0_mul_apply]
    simp only [ih, hu, hu2, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
end Formalism.FourierDecayAlt.P.Wd8
