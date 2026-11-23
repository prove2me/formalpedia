-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crMinor_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:42:44.603459+00:00
-- url     : https://prove2.me/submissions/fb30f335-e278-4a9e-9745-949713b2c66b

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
theorem _root_.solution (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (τ : T) (kk : Fin (r τ))
    (w : Letter T r n → ℕ) (D : ℕ)
    (hw : ∀ π : Equiv.Perm (Fin (kk.val + 1)),
      ∑ j, w ⟨τ, Fin.castLE kk.isLt (π j), β ⟨τ, Fin.castLE kk.isLt j⟩⟩ = D) :
    IsWeightedHomogeneous w (crMinor r n R β τ kk).det D := by
  rw [Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun π _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← hw π]
  refine IsWeightedHomogeneous.prod _ _ _ fun j _ => ?_
  apply isWeightedHomogeneous_X
end Formalism.L2.Pj.Crude
