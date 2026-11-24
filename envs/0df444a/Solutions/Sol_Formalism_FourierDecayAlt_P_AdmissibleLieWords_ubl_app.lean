-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:41:36.687975+00:00
-- url     : https://prove2.me/submissions/89a90d8a-aa49-46d9-8604-bb3177bb64b7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_lss_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ub_app


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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F} {n ea eb γ : ℕ} (ha : UBL a S n ea γ) (hb : UBL b S n eb γ) :
    UBL (fun g => a g (b g)) S n (ea + eb) γ := by
  obtain ⟨⟨Ca, hCa, hua⟩, hla⟩ := ha
  obtain ⟨⟨Cb, hCb, hub⟩, hlb⟩ := hb
  exact ⟨⟨2 ^ n * (Ca * Cb), by positivity, ub_app hSG hla hlb hCa hCb hua hub⟩, lss_app hla hlb⟩
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
