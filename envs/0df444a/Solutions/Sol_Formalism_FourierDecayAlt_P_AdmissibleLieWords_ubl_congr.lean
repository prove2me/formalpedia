-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:43:30.96024+00:00
-- url     : https://prove2.me/submissions/9ac59236-2bc0-48f6-b8a4-4491b0611a21

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_lss_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ub_congr


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
theorem _root_.solution {f f₂ : Mat k r → E} {S V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V) (hSG : S ⊆ GV k r)
    (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) {n e γ : ℕ} (h : UBL f₂ S n e γ) : UBL f S n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, ub_congr hV hSV hSG he hub⟩, lss_congr hV hSV he hl⟩
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
