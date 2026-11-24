-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.ins_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:08:12.394362+00:00
-- url     : https://prove2.me/submissions/9bc539af-e892-41b4-95c0-3837ab8c4052

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_mem_matSub
import Theorems.Thm_Formalism_FourierDecayAlt_P5_eU_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {S : Type} [Fintype S] [DecidableEq S] (C : Subalgebra ℂ A)
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (a : S) {M : M2 (SlopeTestRemainingChoices S A)} (hM : M ∈ matSub (matSub C (Ix S)) (Fin 2)) :
    ins a M ∈ matSub C (Ix S) := by
  unfold ins
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (eU_mem C a i j) ?_
  exact mem_matSub.1 hM i j
end Formalism.FourierDecayAlt.P5
