-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.proj_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:30:18.506438+00:00
-- url     : https://prove2.me/submissions/0fb08737-c55e-4013-9877-3363667e48ba

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
import Theorems.Thm_Formalism_IndefR_DeterminantProjection_unitary_of_proj
import Theorems.Thm_P2M_Formalism_IndefR_DeterminantProjection_proj_idem__4c248bb24d62
import Theorems.Thm_Formalism_IndefR_DeterminantProjection_proj_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.DeterminantProjection
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.IndefR.DeterminantProjection
theorem _root_.solution (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) (hainv : σ ainv = ainv) (x : A) (hx : σ x * x = 1) :
    ((1 + (x - 1) • proj σ J u ainv).map σ)ᵀ * J * (1 + (x - 1) • proj σ J u ainv) = J :=
  unitary_of_proj σ J _ (proj_idem' σ J u ainv ha) (proj_herm σ hσ J hJ u ainv hainv) x hx
end Formalism.IndefR.DeterminantProjection
