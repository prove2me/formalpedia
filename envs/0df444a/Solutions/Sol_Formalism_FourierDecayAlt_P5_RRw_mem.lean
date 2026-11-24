-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.RRw_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:29:20.636221+00:00
-- url     : https://prove2.me/submissions/a7fa4f73-f9cc-45d6-b354-eaed638a640c

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_ins_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P5_transpose_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P5_TTw_mem

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
theorem _root_.solution {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) :
    RRw QQ w ∈ matSub C (Ix S) := by
  induction w with
  | nil =>
    simp only [RRw]
    exact Subalgebra.one_mem _
  | cons l w ih =>
    simp only [RRw]
    refine Subalgebra.mul_mem _ ih (ins_mem C _ ?_)
    split_ifs
    · exact TTw_mem C hQ w _
    · exact transpose_mem (TTw_mem C hQ w _)
end Formalism.FourierDecayAlt.P5
