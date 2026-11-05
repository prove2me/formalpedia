-- Prove2me | solution 1 for CountKSat.HostW.size_le_of_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:07:07.894122+00:00
-- url     : https://prove2.me/submissions/09c01850-6483-468b-9bc7-087c82435c7a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host

set_option autoImplicit false
section
open CountKSat CountKSat.HostW
open Groundwork Groundwork.TM Groundwork.Host Turing
variable {M : Stepped (List Bool) (List Bool)}
namespace CountKSat.HostW
theorem _root_.solution {S t : ℕ} {w : List Bool} {s : M.σ} (h : M.Reaches S w s t) : size s ≤ S := by
  cases h with
  | halt _ hs => exact hs
  | step _ hs _ => exact hs
end CountKSat.HostW
