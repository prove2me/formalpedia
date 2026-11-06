-- Prove2me | solution 1 for Complement.stFromGamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:43.226916+00:00
-- url     : https://prove2.me/submissions/5d482131-ff78-4cf7-827d-a0c7255cc843

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Readers
import Definitions.Def_SizeCircuit_Sized
import Definitions.Def_Complement_FromGamma
import Theorems.Thm_Complement_stFromGamma_of
import Theorems.Thm_SizeCircuit_stSizedBy


set_option autoImplicit false
section
section
open Complement
namespace Complement
theorem _root_.solution : StFromGamma := stFromGamma_of SizeCircuit.stSizedBy
end Complement
