-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:23.213161+00:00
-- url     : https://prove2.me/submissions/5bdf867f-4481-459d-9939-9abeaff2cd14

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_app

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {a b : Mat k r → ℂ} {n ea eb γ : ℕ}
    (ha : UBL a S n ea γ) (hb : UBL b S n eb γ) : UBL (fun g => a g * b g) S n (ea + eb) γ := by
  have ha' : UBL (fun g => ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ) (a g)) S n ea γ :=
    ubl_clm _ hSG ha
  have h := ubl_app hSG ha' hb
  convert h using 2
  simp
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
