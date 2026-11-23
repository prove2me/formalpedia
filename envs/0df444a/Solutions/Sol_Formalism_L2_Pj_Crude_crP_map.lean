-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crP_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:37.10408+00:00
-- url     : https://prove2.me/submissions/eb6a378d-61a3-408a-aec6-6e076f19f534

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
theorem _root_.solution (k : Type) [CommRing k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) :
    MvPolynomial.map (Int.castRingHom k) (Pmin r n β a) = crP r n k β a := by
  unfold Pmin crP
  rw [map_prod]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun kk _ => ?_
  have hM : (MvPolynomial.map (Int.castRingHom k)).mapMatrix (crMinor r n ℤ β σ kk) =
      crMinor r n k β σ kk := by
    ext i j
    simp [crMinor, RingHom.mapMatrix_apply]
  rw [map_pow, RingHom.map_det, hM]
end Formalism.L2.Pj.Crude
