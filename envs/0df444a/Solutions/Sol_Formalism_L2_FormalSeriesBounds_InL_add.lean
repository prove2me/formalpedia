-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.InL.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:47.327866+00:00
-- url     : https://prove2.me/submissions/901cb061-12e9-4301-9c15-7ca209a33ceb

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
theorem _root_.solution {l : ℕ} {f g : PowerSeries C} (hf : InL l f) (hg : InL l g) : InL l (f + g) :=
  fun m hm => by rw [map_add, hf m hm, hg m hm, add_zero]
end InL
end Formalism.L2.FormalSeriesBounds
