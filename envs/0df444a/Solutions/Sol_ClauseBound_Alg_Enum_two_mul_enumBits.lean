-- Prove2me | solution 1 for ClauseBound.Alg.Enum.two_mul_enumBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:46.316584+00:00
-- url     : https://prove2.me/submissions/876e14e4-eafd-4c14-b8db-79bf255fb022

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_ClauseBound_Alg_Enum_sum_erase_eq_pairs
import Theorems.Thm_ClauseBound_Alg_Enum_sum_range_eq_sum_pos
import Theorems.Thm_ClauseBound_Alg_Enum_cap_comm
import Theorems.Thm_ClauseBound_Alg_Enum_enumLen_pos

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}
namespace ClauseBound.Alg.Enum
theorem _root_.solution (hN : F.toP.Presents c N 0 0) : 2 * enumBits g F c = N.U := by
  rw [Network.U, sum_erase_eq_pairs, enumBits, sum_range_eq_sum_pos, pairs, sum_filter, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [enumLen_pos]
  split_ifs with h
  · rw [hN.c_eq _ _ h.ne, hN.c_eq _ _ h.ne']
    have := cap_comm hN _ _ h.ne
    change 2 * F.cap c p.1 p.2 = F.cap c p.1 p.2 + F.cap c p.2 p.1
    omega
  · rfl
end ClauseBound.Alg.Enum
