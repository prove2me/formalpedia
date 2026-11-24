-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.lss_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:09.993496+00:00
-- url     : https://prove2.me/submissions/71d9aea1-3008-4613-b114-8467e7e3a4e4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_cd_app


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
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {S : Set (Mat k r)} {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F} (ha : LSS a S) (hb : LSS b S) :
    LSS (fun g => a g (b g)) S := by
  intro g hg
  obtain ⟨a', ha', V₁, hV₁, hg₁, haV⟩ := ha g hg
  obtain ⟨b', hb', V₂, hV₂, hg₂, hbV⟩ := hb g hg
  let R : (F →L[ℂ] E) →L[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ
  refine ⟨fun x => a' x (b' x), ?_, V₁ ∩ V₂, hV₁.inter hV₂, ⟨hg₁, hg₂⟩, ?_⟩
  · exact cd_app (a := fun x => R (a' x)) (R.contDiff.comp ha') hb'
  · intro g' hg' hV
    dsimp only
    rw [haV g' hg' hV.1, hbV g' hg' hV.2]
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
