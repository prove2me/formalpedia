-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorExpansion.det_comm_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:43.368504+00:00
-- url     : https://prove2.me/submissions/435782af-d780-478e-9beb-5b5e7ea41c5a

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_det_comm_Tm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorExpansion
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
namespace Formalism.FourierDecayAlt.P.QuantumMinorExpansion
theorem _root_.solution (hE : GlRel E) {t : ℕ} (a b : Fin t → Fin n) (w v : ℂ) :
    Commute (qdet E w) (qminor E a b v) := by
  unfold qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right (Int.commute_cast _ _) ?_
  refine Commute.list_prod_right _ _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  exact det_comm_Tm E hE _ _ _ _
end Formalism.FourierDecayAlt.P.QuantumMinorExpansion
