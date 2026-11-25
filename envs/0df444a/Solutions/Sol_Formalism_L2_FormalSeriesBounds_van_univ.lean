-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.van_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:16:31.236989+00:00
-- url     : https://prove2.me/submissions/fcf42d7d-470a-4d81-b65b-74a5314ef262

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
theorem _root_.solution {τ : Type} {f : MvPowerSeries τ C} (h : MvPowerSeries.constantCoeff f = 0) :
    Van Set.univ f := by
  intro ν hν
  have hν0 : ν = 0 := by
    ext w
    by_contra hw
    exact hν w (Finsupp.mem_support_iff.2 hw) (Set.mem_univ w)
  subst hν0
  simpa using h
end Formalism.L2.FormalSeriesBounds
