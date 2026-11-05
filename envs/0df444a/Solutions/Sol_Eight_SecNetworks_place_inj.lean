-- Prove2me | solution 1 for Eight.SecNetworks.place_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:06:10.796225+00:00
-- url     : https://prove2.me/submissions/84adc763-5fe0-4539-a24d-ef42d52cdbc5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Clique

set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset
namespace Eight.SecNetworks
theorem _root_.solution {K : ℕ} (w a b : Fin K) (ha : a ≠ w) (hb : b ≠ w) (h : place w a = place w b) : a = b := by
  have := Fin.val_ne_of_ne ha
  have := Fin.val_ne_of_ne hb
  apply Fin.ext
  unfold place at h
  split_ifs at h <;> omega
end Eight.SecNetworks
