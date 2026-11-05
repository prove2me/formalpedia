-- Prove2me | solution 1 for ClauseBound.Boson.op_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:25:20.506645+00:00
-- url     : https://prove2.me/submissions/2e71eb2e-e299-4e72-b744-eaadf6d7717f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text
import Theorems.Thm_ClauseBound_Boson_Text_sum_win
import Theorems.Thm_ClauseBound_Boson_Text_sum_tup_succ
import Theorems.Thm_ClauseBound_Boson_Text_coef_X_mul
import Theorems.Thm_ClauseBound_Boson_Text_nabPos_mon
import Theorems.Thm_ClauseBound_Boson_Text_coef_mon
import Theorems.Thm_ClauseBound_Boson_Text_nord_smul
import Theorems.Thm_ClauseBound_Boson_Text_nord_nil
import Theorems.Thm_ClauseBound_Boson_Text_nord_cons_neg
import Theorems.Thm_ClauseBound_Boson_Text_nord_cons_pos
import Theorems.Thm_ClauseBound_Boson_Text_sum_erase_le
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_ClauseBound_Boson_Text_wt_cons
import Theorems.Thm_ClauseBound_Boson_WickPlus_toFinset_subset_Icc
import Theorems.Thm_ClauseBound_Boson_nop_eq_sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open Text
namespace ClauseBound.Boson
theorem _root_.solution (a : List ℕ) : ∀ (r : ℤ) (π σ : Multiset ℕ) (M : ℕ), 0 ∉ π → 0 ∉ σ → π.sum ≤ M → σ.sum ≤ M →
    op a r π σ = ∑ ks ∈ tup M a.length with ks.sum = -r, wt a ks * coef π (nord ks (mon σ)) := by
  induction a with
  | nil =>
    intro r π σ M _ _ _ _
    show (if r = 0 then one else 0) π σ = _
    rw [sum_filter]
    simp only [List.length_nil, tup, sum_singleton, List.sum_nil, nord_nil, coef_mon]
    by_cases hr : r = 0
    · subst hr
      simp [one, wt]
    · rw [if_neg hr, if_neg (by omega)]
      rfl
  | cons n a ih =>
    intro r π σ M hπ hσ hπM hσM
    show nop n (op a) r π σ = _
    rw [nop_eq_sum n (op a) r π σ (WickPlus.toFinset_subset_Icc hπ hπM) (WickPlus.toFinset_subset_Icc hσ hσM), sum_filter,
      List.length_cons, sum_tup_succ, sum_win]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      have hl1 := (mem_Icc.1 hl).1
      have hb : bet n l = Ring.choose (-(-(l : ℤ)) - 1) (n - 1) := by rw [bet, if_neg (by omega), neg_neg]
      have hN : (-(-(l : ℤ))).toNat = l := by simp
      unfold cre
      by_cases hlπ : l ∈ π
      · rw [if_pos hlπ, ih (r - l) (π.erase l) σ M (fun h => hπ (Multiset.mem_of_mem_erase h)) hσ (le_trans (sum_erase_le π l) hπM) hσM,
          sum_filter, mul_sum]
        refine sum_congr rfl fun ks _ => ?_
        have hc : (-(l : ℤ) :: ks).sum = -r ↔ ks.sum = -(r - l) := by
          rw [List.sum_cons]; constructor <;> intro h <;> omega
        rw [if_congr hc rfl rfl, nord_cons_neg (by omega), coef_X_mul, hN, if_pos hlπ, wt_cons, hb]
        split_ifs
        · ring
        · ring
      · rw [if_neg hlπ, mul_zero]
        symm
        refine sum_eq_zero fun ks _ => ?_
        rw [nord_cons_neg (by omega), coef_X_mul, hN, if_neg hlπ, mul_zero, ite_self]
    · refine sum_congr rfl fun k hk => ?_
      have hk1 := (mem_Icc.1 hk).1
      have hb : bet n (-(k : ℤ)) = Ring.choose (-(k : ℤ) - 1) (n - 1) := by rw [bet, if_neg (by omega)]
      unfold ann
      rw [ih (r + k) π (σ.erase k) M hπ (fun h => hσ (Multiset.mem_of_mem_erase h)) hπM (le_trans (sum_erase_le σ k) hσM), sum_filter,
        mul_sum, mul_sum]
      refine sum_congr rfl fun ks _ => ?_
      have hc : ((k : ℤ) :: ks).sum = -r ↔ ks.sum = -(r + k) := by
        rw [List.sum_cons]; constructor <;> intro h <;> omega
      rw [if_congr hc rfl rfl, nord_cons_pos (by omega), nabPos_mon, nord_smul, coef_smul, wt_cons, hb]
      split_ifs
      · ring
      · ring
end ClauseBound.Boson
