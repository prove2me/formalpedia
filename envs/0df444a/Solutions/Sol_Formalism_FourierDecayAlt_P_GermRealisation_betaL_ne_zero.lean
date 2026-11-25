-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermRealisation.betaL_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:40:45.861204+00:00
-- url     : https://prove2.me/submissions/22efed2e-7b58-4979-bd79-e649c3b2097e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfFibres
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNegBetaL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRealisation
open Formalism.FourierDecayAlt NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.GermRealisation
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : betaL S ≠ 0 := by
  have hg0 : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg0
  unfold betaL
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) hg.ne')
end Formalism.FourierDecayAlt.P.GermRealisation
