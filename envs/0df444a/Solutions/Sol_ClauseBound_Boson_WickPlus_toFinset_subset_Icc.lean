-- Prove2me | solution 1 for ClauseBound.Boson.WickPlus.toFinset_subset_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:47:14.483051+00:00
-- url     : https://prove2.me/submissions/22b766ac-b14a-4278-8a1d-cd7b6f686838

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_WickPlus

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.WickPlus
open Finset
namespace ClauseBound.Boson.WickPlus
theorem _root_.solution {τ : Multiset ℕ} (h0 : 0 ∉ τ) {M : ℕ} (hM : τ.sum ≤ M) : τ.toFinset ⊆ Icc 1 M := by
  intro x hx
  have hx' := Multiset.mem_toFinset.1 hx
  have h1 : x ≠ 0 := fun h => h0 (h ▸ hx')
  have h2 : x ≤ τ.sum := Multiset.le_sum_of_mem hx'
  exact mem_Icc.2 ⟨by omega, by omega⟩
end ClauseBound.Boson.WickPlus
