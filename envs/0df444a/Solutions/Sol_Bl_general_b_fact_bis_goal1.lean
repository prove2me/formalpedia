-- Prove2me | solution 1 for Bl.general_b_fact_bis.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:31.995334+00:00
-- url     : https://prove2.me/submissions/37023161-9acc-41f0-b618-84b33d16445b

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactBis_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_bis
namespace Bl.general_b_fact_bis
theorem _root_.solution :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) := by
  intro x m h
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← WithBot.coe_natCast] at h
    exact absurd h.symm WithBot.coe_ne_bot
  | coe e =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    rw [← WithBot.coe_natCast, WithBot.coe_inj]
    induction e using ENat.recTopCoe with
    | top =>
      rw [top_add] at h
      exact absurd h.symm (ENat.natCast_ne_top _)
    | coe n =>
      rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_inj] at h
      rw [ENat.natCast_inj]
      omega
end Bl.general_b_fact_bis
