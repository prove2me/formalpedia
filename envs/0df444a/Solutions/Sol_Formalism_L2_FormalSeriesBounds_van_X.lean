-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.van_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:17.137534+00:00
-- url     : https://prove2.me/submissions/6406a144-d545-41af-837b-605acbb66c97

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {τ : Type} {T : Set τ} {s : τ} (hs : s ∈ T) : Van T (X s : MvPowerSeries τ C) := by
  intro ν hν
  rw [coeff_X, if_neg]
  intro h
  exact hν s (by rw [h]; simp) hs
end Formalism.L2.FormalSeriesBounds
