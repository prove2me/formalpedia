-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GeneralGermZero.pairK_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:06:08.839082+00:00
-- url     : https://prove2.me/submissions/b9bfb1b9-5f2e-4e69-beff-28f5e97b38af

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero

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
open Formalism.L2.FormalSeriesBounds.GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
namespace Formalism.L2.FormalSeriesBounds.GeneralGermZero
theorem _root_.solution {σ : Type} {a b : κ → MvPowerSeries σ C} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ q : Fin 2 × κ, MvPowerSeries.constantCoeff (![a, b] q.1 q.2) = 0 := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]
end Formalism.L2.FormalSeriesBounds.GeneralGermZero
