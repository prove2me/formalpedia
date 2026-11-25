-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_dnL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:26.484802+00:00
-- url     : https://prove2.me/submissions/06c1baa3-b371-4c73-be43-1edf355fe8aa

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
theorem _root_.solution (l : ℕ) (f : PowerSeries C) (n : ℕ) :
    PowerSeries.coeff n (dnL l f) = PowerSeries.coeff (l * n) f := by
  unfold dnL
  rw [PowerSeries.coeff_mk]
end Formalism.L2.FormalSeriesBounds
