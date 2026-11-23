-- Prove2me | solution 1 for Formalism.UG.P.spherical_upper_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:15.669156+00:00
-- url     : https://prove2.me/submissions/df44854f-8054-4931-9662-571fb4189d73

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
theorem _root_.solution (b c : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hc : (c : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((b * c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  rw [Units.val_mul]; exact hb.mul hc
end Formalism.UG.P
