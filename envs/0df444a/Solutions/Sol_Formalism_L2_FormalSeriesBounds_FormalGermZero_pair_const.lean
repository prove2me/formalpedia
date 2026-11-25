-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.pair_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:00.593937+00:00
-- url     : https://prove2.me/submissions/8c9496db-5228-4f93-902f-2390c5e4159d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree

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
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution {σ : Type} {a b : Fin dd → MvPowerSeries σ C} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (![a, b] q.1 q.2) = 0 := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]
end Formalism.L2.FormalSeriesBounds.FormalGermZero
