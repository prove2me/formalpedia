-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermFibreKernels.PKer.inner_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:00:53.833973+00:00
-- url     : https://prove2.me/submissions/d1e6ef52-6315-4c6c-93cb-9c37ef1b1e6d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FmSmulLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermFibreKernels
open scoped InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
open Formalism.FourierDecayAlt.P.GermFibreKernels.PKer
variable {α : Type} (P : PKer α)
namespace Formalism.FourierDecayAlt.P.GermFibreKernels.PKer
theorem _root_.solution (x y : α) : ⟪P.vec x, P.vec y⟫_ℂ = P.K x y := by
  unfold vec
  refine (UniformSpace.Completion.inner_coe (𝕜 := ℂ) _ _).trans ?_
  show P.fm (Finsupp.single x 1) (Finsupp.single y 1) = P.K x y
  unfold fm
  simp
end Formalism.FourierDecayAlt.P.GermFibreKernels.PKer
