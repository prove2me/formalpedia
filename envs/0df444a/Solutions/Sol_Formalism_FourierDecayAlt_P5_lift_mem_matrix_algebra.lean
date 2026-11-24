-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.lift_mem_matrix_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:25.864239+00:00
-- url     : https://prove2.me/submissions/277dec61-117f-4190-ab23-4fd22fdd708a

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_mem_matSub
import Theorems.Thm_Formalism_FourierDecayAlt_P5_io_mem

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
theorem _root_.solution {M : M2 A} (hM : ∀ i j, M i j ∈ C) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  rw [mem_matSub]
  intro i j
  simp only [lift0, Matrix.map_apply]
  exact io_mem C (hM i j)
end Formalism.FourierDecayAlt.P5
