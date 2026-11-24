-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:24:58.933802+00:00
-- url     : https://prove2.me/submissions/295edfb5-9bd9-43bb-8bab-b7a48e310400

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_admissible_word_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_congr_loc


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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {f f₂ : Mat k r → E} {S : Set (Mat k r)} {V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V)
    (hSG : S ⊆ GV k r) (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f₂ S n C e γ) :
    UB f S n C e γ := by
  intro w hw g hg
  rw [Dw_congr_loc (admissible_word_mem_lie hw) hV he g (hSG hg) (hSV hg)]
  exact h w hw g hg
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
