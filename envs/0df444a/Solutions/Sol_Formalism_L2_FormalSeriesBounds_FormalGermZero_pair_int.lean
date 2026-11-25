-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.pair_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:51.9518+00:00
-- url     : https://prove2.me/submissions/278721be-090a-4687-ad4b-abfd80cba118

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
theorem _root_.solution {V : VF C} {σ : Type} {a b : Fin dd → MvPowerSeries σ C} (ha : ∀ j, IntS V (a j))
    (hb : ∀ j, IntS V (b j)) : ∀ q : Fin 2 × Fin dd, IntS V (![a, b] q.1 q.2) := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]
end Formalism.L2.FormalSeriesBounds.FormalGermZero
