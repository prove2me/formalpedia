-- Prove2me | solution 1 for ClauseBound.Inst.Half.Pad.padOp_le_padKF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:19.1899+00:00
-- url     : https://prove2.me/submissions/3523fc1c-06dd-4a59-bddf-cc2d400e7e6e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad
namespace ClauseBound.Inst.Half.Pad
theorem _root_.solution (W Δ h s L : ℕ) : padOp W Δ L ≤ padKF W Δ h s L := by
  unfold padOp padKF
  have h1 : Δ ^ 2 * (3 * ((4 * W + 1) * L) + 10) ≤ Δ ^ 2 * (3 * (s + (4 * W + 1) * L) + 10) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : Δ ^ 2 * (3 * (s + (4 * W + 1) * L) + 10) + 4 ≤ (h + 1) * (Δ ^ 2 * (3 * (s + (4 * W + 1) * L) + 10) + 4) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega
end ClauseBound.Inst.Half.Pad
