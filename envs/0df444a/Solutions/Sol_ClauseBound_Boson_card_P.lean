-- Prove2me | solution 1 for ClauseBound.Boson.card_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:41:51.158546+00:00
-- url     : https://prove2.me/submissions/19321b65-015b-4040-841d-8d3e14b63679

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Basic

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open Basic
namespace ClauseBound.Boson
theorem _root_.solution (m : ℕ) : #(P m) = Partitions.p m := by
  unfold P Partitions.p
  rw [Finset.card_image_of_injective _ fun q q' h => Nat.Partition.ext h, Finset.card_univ]
end ClauseBound.Boson
