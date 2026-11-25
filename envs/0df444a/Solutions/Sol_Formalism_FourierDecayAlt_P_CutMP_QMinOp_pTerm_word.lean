-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.QMinOp.pTerm_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:11:08.406566+00:00
-- url     : https://prove2.me/submissions/718ec7ee-005c-42dd-a719-d041e0f1ec75

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatQMinOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.QMinOp
open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp
theorem _root_.solution {P : B.Mat k r → ℂ} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    (pTerm (Wp := Wp) (Wq := Wq) P w).word = w := by
  simp only [pTerm]
  rw [if_pos hw]
end Formalism.FourierDecayAlt.P.CutMP.QMinOp
