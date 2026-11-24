-- Prove2me | solution 1 for Formalism.HN.eq_zero_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:21.734731+00:00
-- url     : https://prove2.me/submissions/a6098a7b-1d41-45de-95fc-8c53fd5e0313

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ρ : V →+ E} {L : Submodule R V}
    (hL : Set.InjOn ρ (L : Set V)) {x : V} (hx : x ∈ L) (h : ρ x = 0) : x = 0 := hL hx L.zero_mem (h.trans (map_zero ρ).symm)
end Formalism.HN
