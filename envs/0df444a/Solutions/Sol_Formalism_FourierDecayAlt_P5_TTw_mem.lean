-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.TTw_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:11:05.337381+00:00
-- url     : https://prove2.me/submissions/c5c9af3f-5959-4791-8ed0-19a646a801a0

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_lift_mem_matrix_algebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_Rh0_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P5_Rht0_mem

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
theorem _root_.solution {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) (Y : ℂ) :
    TTw QQ w Y ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  induction w generalizing Y with
  | nil =>
    simp only [TTw]
    exact lift_mem_matrix_algebra C (hQ Y)
  | cons l w ih =>
    simp only [TTw]
    split_ifs
    · exact Subalgebra.mul_mem _ (ih Y) (Rh0_mem C _ _)
    · exact Subalgebra.mul_mem _ (Rht0_mem C _ _) (ih Y)
end Formalism.FourierDecayAlt.P5
