-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermRealisation.psi_betaL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:00.594281+00:00
-- url     : https://prove2.me/submissions/57299571-9fc9-4e64-925a-66e975c62106

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
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (betaL S) (σ * z) = KB.psiL S σ z := by
  unfold G.psi KB.psiL betaL
  congr 1
  rw [Complex.re_ofReal_mul]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.GermRealisation
