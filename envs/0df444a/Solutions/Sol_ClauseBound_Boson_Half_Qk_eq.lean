-- Prove2me | solution 1 for ClauseBound.Boson.Half.Qk_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:54:37.728705+00:00
-- url     : https://prove2.me/submissions/0eb60521-2f94-45da-9563-cc841ca63a96

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
import Theorems.Thm_ClauseBound_Boson_Half_list_sum_mul_sum
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
theorem _root_.solution (A : FA) (b : List ℕ) (s : ℤ) (π σ : Multiset ℕ) :
    Qk A b s π σ = ∑ i ∈ range (2 * b.sum + 1), ∑ τ ∈ Pz (σ.sum + (b.sum - s - i)),
      fL A b.sum i (fun L => op L (s - b.sum + i) π τ) * op b (b.sum - s - i) τ σ := by
  unfold Qk fL mul2
  refine sum_congr rfl fun i _ => ?_
  rw [list_sum_mul_sum A _ (fun c => c.1 * ((c.2.sum + b.sum).choose i : ℤ)) (fun c τ => op c.2 (s - b.sum + i) π τ)
    (fun τ => op b (b.sum - s - i) τ σ), Finset.mul_sum]
  exact sum_congr rfl fun τ _ => (mul_assoc _ _ _).symm
end ClauseBound.Boson.Half
