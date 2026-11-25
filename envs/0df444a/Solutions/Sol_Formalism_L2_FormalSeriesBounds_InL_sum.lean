-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.InL.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:20.673956+00:00
-- url     : https://prove2.me/submissions/2fe237d0-38a4-45de-9726-98387c448d7b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
namespace InL
theorem _root_.solution {l : ℕ} {ι : Type} (s : Finset ι) (f : ι → PowerSeries C) (hf : ∀ i ∈ s, InL l (f i)) :
    InL l (∑ i ∈ s, f i) :=
  fun m hm => by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i hi => hf i hi m hm
end InL
end Formalism.L2.FormalSeriesBounds
