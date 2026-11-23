-- Prove2me | solution 1 for Formalism.UG.P.spherical_diag_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:15.578799+00:00
-- url     : https://prove2.me/submissions/d878eb75-25ff-4b0f-bdbb-9492f15a445a

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) L) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hji => ?_) (by simp)
  rcases lt_or_gt_of_ne hji with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]
end Formalism.UG.P
