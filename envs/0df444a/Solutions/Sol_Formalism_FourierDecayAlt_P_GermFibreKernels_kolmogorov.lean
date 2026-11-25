-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermFibreKernels.kolmogorov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:59.511475+00:00
-- url     : https://prove2.me/submissions/700bd095-5420-4add-8754-81e8bd91c6f6

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FmSmulLeft
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermFibreKernels_PKer_inner_vec

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
namespace Formalism.FourierDecayAlt.P.GermFibreKernels
theorem _root_.solution {α : Type} (K : α → α → ℂ) (hK : ∀ Y : Finset α, Formalism.FourierDecayAlt.TB.PSDOn Y K) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (V : α → H),
      ∀ x y, K x y = ⟪V x, V y⟫_ℂ :=
  let P : PKer α := ⟨K, hK⟩
  ⟨P.H, inferInstance, inferInstance, inferInstance, P.vec, fun x y => (P.inner_vec x y).symm⟩
end Formalism.FourierDecayAlt.P.GermFibreKernels
