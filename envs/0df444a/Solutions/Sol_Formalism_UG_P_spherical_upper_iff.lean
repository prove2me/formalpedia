-- Prove2me | solution 1 for Formalism.UG.P.spherical_upper_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:57:29.145605+00:00
-- url     : https://prove2.me/submissions/800e40df-ad52-4bea-b9c5-6b1831170c9f

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
theorem _root_.solution (b : GL (Fin n) L) :
    (∀ i j : Fin n, j < i → (b : Matrix (Fin n) (Fin n) L) i j = 0) ↔
      (b : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
  ⟨fun h _ _ hij => h _ _ hij, fun h _ _ hij => h hij⟩
end Formalism.UG.P
