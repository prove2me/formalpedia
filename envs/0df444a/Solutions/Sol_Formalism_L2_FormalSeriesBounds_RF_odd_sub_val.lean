-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.odd_sub_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:29.681509+00:00
-- url     : https://prove2.me/submissions/13d92150-7bc7-424d-8f5e-de4477997ff1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {d : ℕ} [NeZero d] (hd : Even d) (x y : ZMod d) (h : ¬ (Even x.val ↔ Even y.val)) :
    Odd (y - x).val := by
  have h2 : 2 ∣ d := hd.two_dvd
  have e : y = x + (y - x) := by ring
  have e1 : y.val = (x.val + (y - x).val) % d := by
    conv_lhs => rw [e]
    exact ZMod.val_add _ _
  have e2 : y.val % 2 = (x.val + (y - x).val) % 2 := by rw [e1, Nat.mod_mod_of_dvd _ h2]
  rw [Nat.even_iff, Nat.even_iff] at h
  rw [Nat.odd_iff]
  omega
end Formalism.L2.FormalSeriesBounds.RF
