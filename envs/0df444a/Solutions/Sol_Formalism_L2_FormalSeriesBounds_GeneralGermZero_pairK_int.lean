-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GeneralGermZero.pairK_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:16:20.462262+00:00
-- url     : https://prove2.me/submissions/e117804c-b8a3-4425-962b-25a256d532cb

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
theorem _root_.solution {V : VF C} {σ : Type} {a b : κ → MvPowerSeries σ C} (ha : ∀ j, IntS V (a j))
    (hb : ∀ j, IntS V (b j)) : ∀ q : Fin 2 × κ, IntS V (![a, b] q.1 q.2) := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]
end Formalism.L2.FormalSeriesBounds.GeneralGermZero
