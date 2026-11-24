-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.Rht0_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:44:10.022251+00:00
-- url     : https://prove2.me/submissions/8c0cd892-79d7-4e56-baae-95330cd2c077

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
theorem _root_.solution (a : S) (D : ℂ) : (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  have hQ : (Q0 a : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) :=
    mem_matSub.2 fun i j => eU_mem C a i j
  unfold Rht0
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) D) hQ) _
end Formalism.FourierDecayAlt.P5
