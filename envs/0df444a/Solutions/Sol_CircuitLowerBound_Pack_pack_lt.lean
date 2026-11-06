-- Prove2me | solution 1 for CircuitLowerBound.Pack.pack_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:18.077884+00:00
-- url     : https://prove2.me/submissions/5edee2ed-c0e5-412b-827b-ae994dbdbcfd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Pack

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP
open CircuitLowerBound.Pack
variable {e : MCode} {L P : ℕ}
namespace CircuitLowerBound.Pack
theorem _root_.solution {e : MCode} {L r t q : ℕ} (hr : r < 2 ^ rb e) (ht : t < 2 ^ bt e L) (hq : q < 2 ^ bq e L) :
    (r * 2 ^ bt e L + t) * 2 ^ bq e L + q < 2 ^ nb e L := by
  have h1 : r * 2 ^ bt e L + t < 2 ^ rb e * 2 ^ bt e L := by nlinarith
  have h2 : (r * 2 ^ bt e L + t) * 2 ^ bq e L + q < 2 ^ rb e * 2 ^ bt e L * 2 ^ bq e L := by nlinarith
  rwa [nb, pow_add, pow_add]
end CircuitLowerBound.Pack
