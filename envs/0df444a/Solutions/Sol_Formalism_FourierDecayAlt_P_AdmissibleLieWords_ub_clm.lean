-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:47:56.418432+00:00
-- url     : https://prove2.me/submissions/2db30e15-01a0-4f59-80cc-a92577f25d16

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_admissible_word_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dw_clm
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
theorem _root_.solution {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (hSG : S ⊆ GV k r) (hl : LSS f S) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f S n C e γ) :
    UB (fun g => L (f g)) S n (‖L‖ * C) e γ := by
  intro w hw g hg
  obtain ⟨f', hf', V, hV, hgV, hfV⟩ := hl g hg
  have hlie := admissible_word_mem_lie hw
  have e1 := Dw_congr_loc hlie hV (f := fun x => L (f x)) (f₂ := fun x => L (f' x))
    (fun g' hg' hgV' => by rw [hfV g' hg' hgV']) g (hSG hg) hgV
  have e2 := Dw_congr_loc hlie hV hfV g (hSG hg) hgV
  have e3 : Dw w (fun x => L (f' x)) g = L (Dw w f' g) := congrFun (dw_clm L w hf') g
  rw [e1, e3, ← e2, mul_assoc]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h w hw g hg) (norm_nonneg L))
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
