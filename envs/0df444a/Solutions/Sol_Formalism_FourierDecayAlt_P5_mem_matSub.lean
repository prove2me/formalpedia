-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.mem_matSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:05.065723+00:00
-- url     : https://prove2.me/submissions/55beb3c0-72ee-4792-9dbd-509c02415486

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra

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
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution {C : Subalgebra ℂ A} {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n A} :
    M ∈ matSub C n ↔ ∀ i j, M i j ∈ C := by
  exact Iff.rfl
end Formalism.FourierDecayAlt.P5
