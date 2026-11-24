-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.io_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:48:10.323045+00:00
-- url     : https://prove2.me/submissions/a7e5c63f-2326-4a1a-99da-282257be69cc

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
theorem _root_.solution {x : A} (hx : x ∈ C) : (io x : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact C.zero_mem
end Formalism.FourierDecayAlt.P5
