-- Prove2me | solution 1 for ClauseBound.Boson.Half.list_sum_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:49:53.478649+00:00
-- url     : https://prove2.me/submissions/b2b49713-0221-4875-b871-8707925bd910

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
theorem _root_.solution {α ι : Type} (A : List α) (S : Finset ι) (k : α → ℤ) (F : α → ι → ℤ) (G : ι → ℤ) :
    (A.map fun c => k c * ∑ τ ∈ S, F c τ * G τ).sum = ∑ τ ∈ S, (A.map fun c => k c * F c τ).sum * G τ := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
end ClauseBound.Boson.Half
