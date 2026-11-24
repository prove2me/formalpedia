-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.leibC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:04:38.777451+00:00
-- url     : https://prove2.me/submissions/54d65769-c388-4524-9840-55568134d92b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dw_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_leibA


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
theorem _root_.solution (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) (a : Mat k r → (F →L[ℂ] E)) (b : Mat k r → F)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hM : ∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) :
    ‖Dw w (fun g => a g (b g)) g‖ ≤ 2 ^ w.length * M := by
  let R : (F →L[ℂ] E) →L[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ
  have hR : ∀ T : F →L[ℂ] E, ‖R T‖ = ‖T‖ := fun T => ContinuousLinearMap.norm_restrictScalars T
  have hRa : ContDiff ℝ ∞ (fun x => R (a x)) := R.contDiff.comp ha
  have hD : ∀ w₁ : List (Bool × Mat k r), Dw w₁ (fun x => R (a x)) g = R (Dw w₁ a g) :=
    fun w₁ => congrFun (dw_clm R w₁ ha) g
  have key := leibA g M w (fun x => R (a x)) b hRa hb
    (fun w₁ w₂ hs => by rw [hD, hR]; exact hM w₁ w₂ hs)
  exact key
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
