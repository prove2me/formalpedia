-- Prove2me | solution 1 for ClauseBound.Inst.Half.chooseZ_clip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:35:28.096467+00:00
-- url     : https://prove2.me/submissions/5c9900a0-e997-4d58-82ff-0b028b33cf56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Theorems.Thm_ClauseBound_Inst_Rec_chooseZ_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half
theorem _root_.solution (a i : ℕ) : chooseZ (a : ℤ) i = if i ≤ a then chooseZ (a : ℤ) (min i a) else 0 := by
  split_ifs with h
  · rw [min_eq_left h]
  · rw [chooseZ_eq, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (not_le.1 h), Nat.cast_zero]
end ClauseBound.Inst.Half
