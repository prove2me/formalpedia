-- Prove2me | solution 1 for Coding.exists_occOfSlot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:54:19.502867+00:00
-- url     : https://prove2.me/submissions/5f6f5562-1c10-4279-a95e-05a8b4b5f79b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccTests
import Theorems.Thm_Coding_fst_lt_of_mem_occAll
import Theorems.Thm_Coding_length_getD_le
import Theorems.Thm_Coding_mem_occAll
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}
namespace Coding
theorem _root_.solution (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) : ∃ p : Slot 1 Φ.length 3, occOfSlot p = o :=
  ⟨(0, ⟨o.1, fst_lt_of_mem_occAll ho⟩, ⟨o.2, lt_of_lt_of_le (mem_occAll.1 ho) (length_getD_le h3 o.1)⟩), rfl⟩
end Coding
