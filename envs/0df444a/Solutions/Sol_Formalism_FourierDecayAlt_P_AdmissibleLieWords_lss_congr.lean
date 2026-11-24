-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.lss_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:35.099853+00:00
-- url     : https://prove2.me/submissions/99aa86de-cce7-4256-98f9-f4f2dd653508

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe

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
    (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) (h : LSS f₂ S) : LSS f S := by
  intro g hg
  obtain ⟨f', hf', W, hW, hgW, hfW⟩ := h g hg
  refine ⟨f', hf', V ∩ W, hV.inter hW, ⟨hSV hg, hgW⟩, ?_⟩
  intro g' hg' hgVW
  rw [he g' hg' hgVW.1, hfW g' hg' hgVW.2]
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
