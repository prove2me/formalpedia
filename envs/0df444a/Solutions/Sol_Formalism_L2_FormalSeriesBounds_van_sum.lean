-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.van_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:34.668945+00:00
-- url     : https://prove2.me/submissions/439f12a7-013e-47fb-a1d3-4816664020a6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {τ ι : Type} {T : Set τ} (s : Finset ι) (f : ι → MvPowerSeries τ C) (hf : ∀ i ∈ s, Van T (f i)) :
    Van T (∑ i ∈ s, f i) := by
  intro ν hν
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => hf i hi ν hν)
end Formalism.L2.FormalSeriesBounds
