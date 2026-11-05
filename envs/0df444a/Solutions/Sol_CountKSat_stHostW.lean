-- Prove2me | solution 1 for CountKSat.stHostW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:01:23.827498+00:00
-- url     : https://prove2.me/submissions/4e583a1c-119a-4017-a1a3-63b8ea10e5df

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
import Theorems.Thm_CountKSat_exists_tmW

set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.TM Groundwork.Host Turing HostW
namespace CountKSat
theorem _root_.solution : StHostW := fun M _ => exists_tmW M
end CountKSat
