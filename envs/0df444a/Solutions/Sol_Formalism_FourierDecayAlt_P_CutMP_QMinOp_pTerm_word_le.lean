-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.QMinOp.pTerm_word_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:52.638593+00:00
-- url     : https://prove2.me/submissions/8385ac93-dc44-466b-812b-6a6177ae659c

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
theorem _root_.solution (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) :
    (pTerm (Wp := Wp) (Wq := Wq) P w).word.length ≤ w.length := by
  simp only [pTerm]
  split_ifs
  · exact le_refl _
  · simp
end Formalism.FourierDecayAlt.P.CutMP.QMinOp
