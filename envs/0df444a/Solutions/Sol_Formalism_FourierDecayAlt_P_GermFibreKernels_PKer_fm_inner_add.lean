-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermFibreKernels.PKer.fm_inner_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:50.320804+00:00
-- url     : https://prove2.me/submissions/4a7ae60a-49c2-416d-9c27-3719ffec0be7

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
theorem _root_.solution (x : α) (g₁ g₂ : α →₀ ℂ) :
    ((g₁ + g₂).sum fun y b => P.K x y * b) = (g₁.sum fun y b => P.K x y * b) + g₂.sum fun y b => P.K x y * b :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)
end Formalism.FourierDecayAlt.P.GermFibreKernels.PKer
