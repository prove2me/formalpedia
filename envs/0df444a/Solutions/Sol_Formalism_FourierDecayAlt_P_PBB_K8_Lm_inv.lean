-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBB.K8.Lm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:08:37.098805+00:00
-- url     : https://prove2.me/submissions/df4d76c8-e716-4563-966c-3b1813fa19ef

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramLocTendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBB Formalism.FourierDecayAlt.P.PBB.K8
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBB.K8
theorem _root_.solution (g : ℕ) (hg : (g : ℝ) ≠ 0) (w : ℂ) : Lm g ((((-(g : ℝ) / 2 : ℝ)) : ℂ) * conj w) = w := by
  simp only [Lm, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  rw [← mul_assoc, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
  have : (-(2 / (g : ℝ)) * (-(g : ℝ) / 2)) = 1 := by field_simp
  rw [this]
  simp
end Formalism.FourierDecayAlt.P.PBB.K8
