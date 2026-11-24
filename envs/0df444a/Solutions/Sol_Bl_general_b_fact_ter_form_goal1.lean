-- Prove2me | solution 1 for Bl.general_b_fact_ter_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:04.190118+00:00
-- url     : https://prove2.me/submissions/cc160e8a-ae76-4abc-82de-5b66ecf4bd93

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_ter_form
namespace Bl.general_b_fact_ter_form
theorem _root_.solution :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) := by
  intro x m h
  induction x using WithBot.recBotCoe with
  | bot =>
    exfalso
    have e : ((m + 1 : ℕ) : WithBot ENat) = (((m : ENat) + 1 : ENat) : WithBot ENat) := by
      push_cast
      rfl
    have hb : (⊥ : WithBot ENat) + 1 = ⊥ := WithBot.bot_add _
    rw [e, hb] at h
    exact WithBot.bot_ne_coe h
  | coe y =>
    have h2 : ((y + 1 : ENat) : WithBot ENat) = (((m : ENat) + 1 : ENat) : WithBot ENat) := by
      rw [WithBot.coe_add, WithBot.coe_one]
      rw [h]
      push_cast
      rfl
    have h3 : y + 1 = (m : ENat) + 1 := WithBot.coe_injective h2
    have h4 : y = (m : ENat) := by
      have := (ENat.add_left_injective_of_ne_top (n := 1) ENat.one_ne_top) h3
      exact this
    rw [h4]
    rfl
end Bl.general_b_fact_ter_form
