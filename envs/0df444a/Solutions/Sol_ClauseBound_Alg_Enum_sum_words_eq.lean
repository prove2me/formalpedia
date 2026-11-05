-- Prove2me | solution 1 for ClauseBound.Alg.Enum.sum_words_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:37:09.221591+00:00
-- url     : https://prove2.me/submissions/5ba35756-d05c-41fb-b603-985c6e20958b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_ClauseBound_Alg_Enum_pos_bijOn
import Theorems.Thm_Groundwork_Code_sum_dec
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_length_chunkAt
import Theorems.Thm_Groundwork_mem_words
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}
namespace ClauseBound.Alg.Enum
theorem _root_.solution (g : ℕ) (F : FNet C) (c : C) (G : (Fin g × Fin g → List Bool) → ℤ) :
    ∑ w ∈ words (enumBits g F c), G (fun p => chunkAt (enumLen g F c) (pos p) w) =
      ∑ t ∈ tuples (fun _ : Fin g × Fin g => True) (fun p => words (enumLen g F c (pos p))) [], G t := by
  have hD : ((words (enumBits g F c)).filter fun w => ∀ p : Fin g × Fin g, True →
      chunkAt (enumLen g F c) (pos p) w ∈ words (enumLen g F c (pos p))) = words (enumBits g F c) :=
    filter_true_of_mem fun w hw p _ =>
      mem_words.2 (length_chunkAt _ (mem_range.1 (mem_coe.1 (pos_bijOn.mapsTo trivial))) (mem_words.1 hw))
  have h := (Code.seq (fun _ : Fin g × Fin g => True) pos (g * g) pos_bijOn (enumLen g F c)
    (fun p => words (enumLen g F c (pos p))) (fun _ => id) (fun _ _ _ hw => mem_words.1 hw) (fun _ _ => Set.bijOn_id _) []).sum_dec G
  rw [← h]
  refine (sum_congr hD.symm fun w _ => congrArg G (funext fun p => ?_))
  change _ = if True then id (chunkAt (enumLen g F c) (pos p) w) else []
  rw [if_pos trivial]
  rfl
end ClauseBound.Alg.Enum
