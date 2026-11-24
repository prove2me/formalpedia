-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.eU_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:48:31.153736+00:00
-- url     : https://prove2.me/submissions/f82806be-2aad-45cc-ac22-5ea9c66ff513

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_mem_matSub

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
theorem _root_.solution (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro x y
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact C.one_mem
  · exact C.zero_mem
end Formalism.FourierDecayAlt.P5
