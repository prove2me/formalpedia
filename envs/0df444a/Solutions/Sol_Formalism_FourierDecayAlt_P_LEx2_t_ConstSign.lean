-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_ConstSign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:32:48.331325+00:00
-- url     : https://prove2.me/submissions/3f5716f7-68c4-4a88-abb1-da4d4829261f

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : ConstSign := by
  classical
  intro n lam α β hR
  suffices h : ∀ T : Finset (Fin n), ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧
      ∀ Y ∈ Set.Icc α β, |∏ s ∈ T, (Y + lam s)| = sg * ∏ s ∈ T, (Y + lam s) from h Finset.univ
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨1, Or.inl rfl, fun Y _ => by simp⟩
  | insert s T hs ih =>
    obtain ⟨sg, hsg, h⟩ := ih
    have hcase : (∀ Y ∈ Set.Icc α β, 0 < Y + lam s) ∨ (∀ Y ∈ Set.Icc α β, Y + lam s < 0) := by
      by_cases h1 : -lam s < α
      · left; intro Y hY; linarith [hY.1]
      · by_cases h2 : β < -lam s
        · right; intro Y hY; linarith [hY.2]
        · exact absurd ⟨not_lt.mp h1, not_lt.mp h2⟩ (hR s)
    rcases hcase with hp | hn
    · refine ⟨sg, hsg, fun Y hY => ?_⟩
      rw [Finset.prod_insert hs, abs_mul, h Y hY, abs_of_pos (hp Y hY)]; ring
    · refine ⟨-sg, by rcases hsg with rfl | rfl <;> simp, fun Y hY => ?_⟩
      rw [Finset.prod_insert hs, abs_mul, h Y hY, abs_of_neg (hn Y hY)]; ring
end Formalism.FourierDecayAlt.P.LEx2
