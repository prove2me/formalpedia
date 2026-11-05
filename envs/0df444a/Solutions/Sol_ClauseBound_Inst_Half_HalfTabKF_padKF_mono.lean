-- Prove2me | solution 1 for ClauseBound.Inst.Half.HalfTabKF.padKF_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:24:07.269716+00:00
-- url     : https://prove2.me/submissions/c8337ce1-ba39-4309-9b22-6f291f60bcc1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabKF
namespace ClauseBound.Inst.Half.HalfTabKF
theorem _root_.solution (W Δ h : ℕ) {s s' L L' : ℕ} (hs : s ≤ s') (hL : L ≤ L') : padKF W Δ h s L ≤ padKF W Δ h s' L' := by
  unfold padKF
  gcongr
end ClauseBound.Inst.Half.HalfTabKF
