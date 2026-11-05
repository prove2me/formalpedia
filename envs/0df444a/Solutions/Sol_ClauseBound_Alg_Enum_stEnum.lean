-- Prove2me | solution 1 for ClauseBound.Alg.Enum.stEnum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:52:44.377016+00:00
-- url     : https://prove2.me/submissions/ac03baad-65e3-49ab-8665-ff6b16e2225b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_ClauseBound_Alg_Enum_value_eq_sum_labels
import Theorems.Thm_ClauseBound_Alg_Enum_two_mul_enumBits
import Theorems.Thm_ClauseBound_Alg_Enum_tuples_eq
import Theorems.Thm_ClauseBound_Alg_Enum_sum_words_eq
import Theorems.Thm_ClauseBound_Alg_Enum_term_eq
import Theorems.Thm_ClauseBound_Alg_Enum_enumF_eq
import Theorems.Thm_Groundwork_SatNet_term_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
namespace ClauseBound.Alg.Enum
theorem _root_.solution : StEnum := by
  intro C pad g F c N hN hE hn
  refine ⟨?_, two_mul_enumBits hN⟩
  rw [value_eq_sum_labels N [], sum_congr rfl (term_eq hN), tuples_eq hN, ← sum_words_eq]
  exact enumF_eq pad g F c hE hn
end ClauseBound.Alg.Enum
