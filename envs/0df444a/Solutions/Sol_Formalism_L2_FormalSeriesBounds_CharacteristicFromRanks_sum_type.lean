-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.sum_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:57:07.307796+00:00
-- url     : https://prove2.me/submissions/e9123084-6ceb-46df-81de-91b17d5b646d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks

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
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
theorem _root_.solution {ι : Type} [Fintype ι] (P : ι → Prop) {m : ℕ} (e : Fin m ≃ {x // P x})
    (F : ι → C) (hF : ∀ x, ¬ P x → F x = 0) : ∑ c, F (e c) = ∑ x, F x := by
  rw [show (∑ c, F (e c)) = ∑ s : {x // P x}, F s from Equiv.sum_comp e (fun s => F s),
    ← Finset.sum_subtype (Finset.univ.filter P) (by simp) F, Finset.sum_filter_of_ne]
  intro x _ hx
  by_contra hP
  exact hx (hF x hP)
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
