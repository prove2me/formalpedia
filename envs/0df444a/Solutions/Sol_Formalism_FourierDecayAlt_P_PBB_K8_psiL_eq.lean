-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBB.K8.psiL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:06:46.435407+00:00
-- url     : https://prove2.me/submissions/ce7d4415-d47c-4464-82d5-59663bbd4736

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
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (l c z : ℂ) :
    z * KB.psiL S l c = 𝐞 (-⟪c, Lm S.g l⟫) • z := by
  rw [Circle.smul_def, Real.fourierChar_apply, KB.psiL, mul_comm z]
  congr 2
  have hi : ⟪c, Lm S.g l⟫ = -(2 / (S.g : ℝ)) * (l * c).re := by
    simp [Lm, Complex.inner, Complex.mul_re]
    ring
  rw [hi]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.PBB.K8
