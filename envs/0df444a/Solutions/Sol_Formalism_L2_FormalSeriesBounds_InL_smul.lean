-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.InL.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:32.361803+00:00
-- url     : https://prove2.me/submissions/b06abade-fc6b-4a29-a6e6-28996b79c27d

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
theorem _root_.solution {l : ℕ} {f : PowerSeries C} (hf : InL l f) (c : C) : InL l (c • f) :=
  fun m hm => by rw [PowerSeries.coeff_smul, hf m hm, smul_zero]
end InL
end Formalism.L2.FormalSeriesBounds
