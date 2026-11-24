-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.transpose_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:47:56.07552+00:00
-- url     : https://prove2.me/submissions/004fc8d1-8233-4fbe-a640-e686a9a59b10

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
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {C' : Subalgebra ℂ A} {M : Matrix n n A}
    (hM : M ∈ matSub C' n) : Mᵀ ∈ matSub C' n := by
  exact mem_matSub.2 fun i j => mem_matSub.1 hM j i
end Formalism.FourierDecayAlt.P5
