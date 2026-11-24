-- Prove2me | solution 1 for Formalism.UG.P.spherical_diag_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:50.447575+00:00
-- url     : https://prove2.me/submissions/2a9ca681-9a32-4758-bcb8-a9700f4a0c85

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
theorem _root_.solution (b : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (i : Fin n) : (b : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  have hd : (b : Matrix (Fin n) (Fin n) L).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
    exact this.ne_zero
  rw [Matrix.det_of_isUpperTriangular hb] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)
end Formalism.UG.P
