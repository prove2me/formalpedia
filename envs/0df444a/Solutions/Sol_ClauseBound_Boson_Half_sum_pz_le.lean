-- Prove2me | solution 1 for ClauseBound.Boson.Half.sum_pz_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:52:36.561011+00:00
-- url     : https://prove2.me/submissions/8ed86834-35b3-4961-8564-8b7574d01805

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_HalfSum
import Definitions.Def_ClauseBound_Rec_Number
import Definitions.Def_ClauseBound_Boson_Half
import Theorems.Thm_ClauseBound_Boson_HalfSum_coe_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_pos_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_sum_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_zero_notMem_parts


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Half
open HalfSum (coe_lst sum_lst pos_lst zero_notMem_parts)
namespace ClauseBound.Boson.Half
theorem _root_.solution {h : ℕ} (t : ℕ → ℤ) (hinj : ∀ i j, t i = t j → i = j) (hle : ∀ i ∈ range (2 * h + 1), t i ≤ 4 * h) :
    ∑ i ∈ range (2 * h + 1), ClauseBound.Part.pz (t i) ≤ ∑ E ∈ range (4 * h + 1), Partitions.p E := by
  have h1 : ∑ i ∈ range (2 * h + 1), ClauseBound.Part.pz (t i) = ∑ i ∈ (range (2 * h + 1)).filter (fun i => 0 ≤ t i), Partitions.p (t i).toNat := by
    rw [sum_filter]
    exact sum_congr rfl fun i _ => rfl
  rw [h1, ← sum_image (f := Partitions.p) (g := fun i => (t i).toNat)]
  · refine sum_le_sum_of_subset fun E hE => ?_
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hE
    have h2 := hle i (mem_filter.1 hi).1
    exact mem_range.2 (by omega)
  · intro i hi j hj hij
    have hi' := (mem_filter.1 (mem_coe.1 hi)).2
    have hj' := (mem_filter.1 (mem_coe.1 hj)).2
    exact hinj i j (by have : (t i).toNat = (t j).toNat := hij; omega)
end ClauseBound.Boson.Half
