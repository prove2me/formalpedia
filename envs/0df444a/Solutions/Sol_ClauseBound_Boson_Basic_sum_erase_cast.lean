-- Prove2me | solution 1 for ClauseBound.Boson.Basic.sum_erase_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:04.035248+00:00
-- url     : https://prove2.me/submissions/e88d1a25-5752-4f0e-88cc-b1af5294ebca

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
open ClauseBound.Boson.Basic
namespace ClauseBound.Boson.Basic
theorem _root_.solution {π : Multiset ℕ} {l : ℕ} (h : l ∈ π) : ((π.erase l).sum : ℤ) = π.sum - l := by
  have := Multiset.sum_erase h
  omega
end ClauseBound.Boson.Basic
