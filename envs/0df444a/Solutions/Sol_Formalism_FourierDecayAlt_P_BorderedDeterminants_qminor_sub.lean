-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BorderedDeterminants.qminor_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:58:44.669466+00:00
-- url     : https://prove2.me/submissions/61bb56d9-bc02-4064-b4dc-60eea6a466e5

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants
import Theorems.Thm_Formalism_FourierDecayAlt_P_BorderedDeterminants_Tm_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BorderedDeterminants
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.BorderedDeterminants
theorem _root_.solution {n t : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (a b : Fin t → Fin n) (u : ℂ) :
    qminor (subA E) a b u = qminor E (Fin.castSucc ∘ a) (Fin.castSucc ∘ b) u := by
  simp only [qminor, Tm_sub, Function.comp_apply]
end Formalism.FourierDecayAlt.P.BorderedDeterminants
