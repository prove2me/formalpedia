-- Prove2me | solution 1 for Formalism.UG.P.gLoc_range_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:20:19.05432+00:00
-- url     : https://prove2.me/submissions/e9b3fbd4-ccd5-4e2c-a743-b97a59b2f271

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {R : Type} [CommRing R] (S : Subring R) (x : R) :
    x ∈ Set.range S.subtype ↔ x ∈ S := by
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
end Formalism.UG.P
