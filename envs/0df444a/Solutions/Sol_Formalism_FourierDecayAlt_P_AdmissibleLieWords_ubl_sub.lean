-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:27.400722+00:00
-- url     : https://prove2.me/submissions/a0edbd77-c238-4b55-95b6-3e305318faf1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_lss_mono


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
theorem _root_.solution {f : Mat k r → E} {S S' : Set (Mat k r)} (hS : S' ⊆ S) {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL f S' n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, fun w hw g hg => hub w hw g (hS hg)⟩, lss_mono hl hS⟩
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
