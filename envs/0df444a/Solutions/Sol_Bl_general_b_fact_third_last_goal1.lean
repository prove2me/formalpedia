-- Prove2me | solution 1 for Bl.general_b_fact_third_last.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:06.176128+00:00
-- url     : https://prove2.me/submissions/f21cbd5f-39a1-4e8c-938a-46e348cfe8f7

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdLast_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_last
namespace Bl.general_b_fact_third_last
theorem _root_.solution :
  ∀ {a : WithBot.{0} ENat} {n : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} a 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} n 1)) → Eq.{1} a (Nat.cast.{0} n) := by
  intro a n h
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add, ← WithBot.coe_natCast] at h
    exact WithBot.bot_ne_coe h
  | coe e =>
    have h1 : ((e + 1 : ENat) : WithBot ENat) = (((n : ENat) + 1 : ENat) : WithBot ENat) := by
      rw [WithBot.coe_add, WithBot.coe_one, WithBot.coe_add, WithBot.coe_one, WithBot.coe_natCast, h]
      push_cast
      rfl
    have h2 : e + 1 = (n : ENat) + 1 := WithBot.coe_injective h1
    have h3 : e = (n : ENat) := ENat.add_left_injective_of_ne_top ENat.one_ne_top h2
    rw [h3, WithBot.coe_natCast]
end Bl.general_b_fact_third_last
