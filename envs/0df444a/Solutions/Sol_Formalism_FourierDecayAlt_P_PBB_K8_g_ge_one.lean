-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBB.K8.g_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:08:39.868632+00:00
-- url     : https://prove2.me/submissions/f26f7186-512a-42ca-8099-afff043463df

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
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : (1 : ℝ) ≤ S.g := by
  have : 1 ≤ S.g := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg1.ne' hg2.ne')
  exact_mod_cast this
end Formalism.FourierDecayAlt.P.PBB.K8
