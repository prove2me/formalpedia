-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.InL.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:39.015892+00:00
-- url     : https://prove2.me/submissions/842e93b5-88fd-4d13-a835-85da33fd2e17

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
theorem _root_.solution {l : ℕ} {f g : PowerSeries C} (hf : InL l f) (hg : InL l g) : InL l (f - g) :=
  fun m hm => by rw [map_sub, hf m hm, hg m hm, sub_zero]
end InL
end Formalism.L2.FormalSeriesBounds
