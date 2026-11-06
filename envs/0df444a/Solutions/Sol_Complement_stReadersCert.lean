-- Prove2me | solution 1 for Complement.stReadersCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:19:38.105895+00:00
-- url     : https://prove2.me/submissions/88d4917c-12cd-426e-bcb5-e246b3369a7e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Sets
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Mathlib.Tactic
import Definitions.Def_Complement_Readers
import Theorems.Thm_Complement_readers_aux
import Theorems.Thm_GraphProblems_stCertRead


set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems
namespace Complement
theorem _root_.solution : StReadersCert := readers_aux stCertRead.2
end Complement
