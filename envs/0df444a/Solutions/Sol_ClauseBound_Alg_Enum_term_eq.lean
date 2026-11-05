-- Prove2me | solution 1 for ClauseBound.Alg.Enum.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:01.704013+00:00
-- url     : https://prove2.me/submissions/4277e655-6986-472a-a9b0-fd7acf571ed0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_ClauseBound_Alg_Enum_W_eq
import Theorems.Thm_ClauseBound_Alg_Enum_f_eq
import Theorems.Thm_ClauseBound_Alg_Enum_cap_comm
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_pr_of_lt
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}
namespace ClauseBound.Alg.Enum
theorem _root_.solution (hN : F.toP.Presents c N 0 0) (t : Fin g × Fin g → List Bool)
    (ht : t ∈ tuples (fun p : Fin g × Fin g => p.1 < p.2) (fun p => N.lab p.1 p.2) []) :
    ∏ a, ∑ z ∈ N.S a, N.W a z * ∏ b ∈ univ.erase a, N.f a b z (t (pr a b)) = term F c t := by
  unfold term
  refine prod_congr rfl fun a _ => ?_
  have hS : N.S a = words (F.n c a) := hN.S_eq a
  rw [hS]
  refine sum_congr rfl fun z hz => ?_
  rw [W_eq hN a z (mem_words.1 hz)]
  congr 1
  refine prod_congr rfl fun b hb => ?_
  have hab : a ≠ b := (ne_of_mem_erase hb).symm
  refine (f_eq hN a b z _ hab (mem_words.1 hz) ?_).symm
  rcases lt_or_gt_of_ne hab with h | h
  · have h1 := ((mem_tuples _ _ _ t).1 ht (a, b)).1 h
    rw [(pr_of_lt h).1]
    rw [show N.lab a b = words (F.cap c a b) from hN.lab_eq a b hab] at h1
    exact mem_words.1 h1
  · have h1 := ((mem_tuples _ _ _ t).1 ht (b, a)).1 h
    rw [(pr_of_lt h).2, cap_comm hN a b hab]
    rw [show N.lab b a = words (F.cap c b a) from hN.lab_eq b a hab.symm] at h1
    exact mem_words.1 h1
end ClauseBound.Alg.Enum
