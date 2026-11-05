-- Prove2me | solution 1 for ClauseBound.Alg.GridPresents.gridW_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:08:07.708657+00:00
-- url     : https://prove2.me/submissions/35ccc686-228d-4581-bcd3-5feb0599f0e8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_ClauseBound_Alg_GridPresents_chkG_iff
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_PaddedDescent_F_prodL_eq
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
namespace ClauseBound.Alg.GridPresents
theorem _root_.solution (p d : ℕ) (tr : Bool) (ℓ : ℕ) (T : Tab) (a : ℕ) (z : List Bool) :
    gridW p d tr ℓ T (a, z) =
      (∏ i : Fin (nMemb p d tr), if (heG p d ℓ z i (nodeG d tr a i)).all (!·) = true then
          look T (nodeG d tr a i, (List.range (p * d)).map fun u => if u = nodeG d tr a i then [] else heG p d ℓ z i u)
        else 0) *
      ∏ q ∈ pairs (Fin (nMemb p d tr)), if heG p d ℓ z q.1 (nodeG d tr a q.2) = heG p d ℓ z q.2 (nodeG d tr a q.1) then 1 else 0 := by
  unfold gridW
  by_cases hc : chkG p d tr ℓ (a, z) = true
  · obtain ⟨h1, h2⟩ := (chkG_iff p d tr ℓ a z).1 hc
    rw [hc, cond_true, Finset.prod_eq_one (s := pairs (Fin (nMemb p d tr))) fun q hq => if_pos (h2 q hq), mul_one, prodL_eq,
      Finset.prod_range]
    exact Finset.prod_congr rfl fun i _ => (if_pos (h1 i)).symm
  · rw [Bool.not_eq_true] at hc
    rw [hc, cond_false]
    have hc' : ¬ chkG p d tr ℓ (a, z) = true := by rw [hc]; exact Bool.false_ne_true
    rw [chkG_iff, not_and_or] at hc'
    rcases hc' with h | h
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hi), zero_mul]
    · push Not at h
      obtain ⟨q, hq, hne⟩ := h
      rw [Finset.prod_eq_zero hq (if_neg hne), mul_zero]
end ClauseBound.Alg.GridPresents
