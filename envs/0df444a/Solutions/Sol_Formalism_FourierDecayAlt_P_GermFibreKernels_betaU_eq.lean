-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermFibreKernels.betaU_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:55.274535+00:00
-- url     : https://prove2.me/submissions/f3c06a81-442e-4dbd-95b2-1969840e5ab0

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNegBetaL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ToStdAppend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermFibreKernels
open Formalism.FourierDecayAlt NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.GermFibreKernels
theorem _root_.solution : U.betaU = 2 * Complex.I := by
  simp [U.betaU, Formalism.QuantumDeterminants.cStd]
end Formalism.FourierDecayAlt.P.GermFibreKernels
