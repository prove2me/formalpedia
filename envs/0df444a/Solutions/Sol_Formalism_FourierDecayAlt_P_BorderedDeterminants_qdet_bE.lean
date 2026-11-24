-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BorderedDeterminants.qdet_bE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:35.282595+00:00
-- url     : https://prove2.me/submissions/027b12a2-239a-4a44-8a32-81ca813545bd

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants
import Theorems.Thm_Formalism_FourierDecayAlt_P_BorderedDeterminants_bS_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_cyc
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds


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
theorem _root_.solution {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (hE : GlRel E) (u : ℂ) :
    qdet E u = qminor E (bE (Fin.last n) Fin.castSucc) (bE (Fin.last n) Fin.castSucc) u := by
  unfold qdet
  rw [← bS_id, ← Qx6.bE_cyc, quantumMinorRowSkew_holds A, quantumMinorColSkew_holds A _ _ E hE, ← mul_assoc, ← Int.cast_mul,
    ← Units.val_mul, Int.units_mul_self]
  simp
end Formalism.FourierDecayAlt.P.BorderedDeterminants
