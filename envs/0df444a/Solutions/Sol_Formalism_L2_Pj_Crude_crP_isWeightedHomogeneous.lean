-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crP_isWeightedHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:01.235182+00:00
-- url     : https://prove2.me/submissions/06e0c6ca-f022-4e86-9539-ad4f911bbb3b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (w : Letter T r n → ℕ) (D : ∀ τ : T, Fin (r τ) → ℕ)
    (hD : ∀ τ kk, IsWeightedHomogeneous w (crMinor r n R β τ kk).det (D τ kk)) :
    IsWeightedHomogeneous w (crP r n R β a) (∑ τ, ∑ kk, crExp r a τ kk • D τ kk) := by
  unfold crP
  exact IsWeightedHomogeneous.prod _ _ _ fun τ _ =>
    IsWeightedHomogeneous.prod _ _ _ fun kk _ => (hD τ kk).pow _
end Formalism.L2.Pj.Crude
