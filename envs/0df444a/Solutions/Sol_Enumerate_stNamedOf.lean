-- Prove2me | solution 1 for Enumerate.stNamedOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:54.965069+00:00
-- url     : https://prove2.me/submissions/0d6178e1-569b-4880-8fbb-682018c1e8fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Mach_LemSparsification
import Definitions.Def_SparsificationLemma_Mach_Len
import Definitions.Def_SparsificationLemma_Mach_Main
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Enumerate_Named
import Theorems.Thm_Enumerate_enumerates_tauOf
import Theorems.Thm_Enumerate_time_le_poly
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Mach_div_le_two_pow_precE
import Theorems.Thm_UniformInK_stParU
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo SparsificationLemma.Mach Turing
namespace Enumerate
theorem _root_.solution : StNamedOf := by
  intro hP hL hE
  obtain ⟨M, C₀, hfin, hM⟩ := hP
  refine ⟨M, hfin, fun ε hε => ?_⟩
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (lt_min hε one_pos)
  have hqε : (q : ℝ) ≤ ε := (hq1.trans_le (min_le_left _ _)).le
  have hs0 : s0U 3 ≤ precE (C₀ + 1) 3 q := le_max_left _ _
  have hsq := div_le_two_pow_precE (C₀ + 1) 3 q
  generalize precE (C₀ + 1) 3 q = s at hs0 hsq
  have hs : ((C₀ + 1 : ℕ) : ℝ) / ε ≤ (2 : ℝ) ^ s :=
    (div_le_iff₀ hε).2 (((div_le_iff₀ hq0).1 hsq).trans (mul_le_mul_of_nonneg_left hqε (by positivity)))
  have hτ : 8 * 3 ≤ tauOf s := ((stParU 3 s (by norm_num)).2 hs0).2
  refine ⟨tauOf s ^ 6, s, C₀ * (s + 412) ^ C₀ + 4 * C₀, Nat.one_le_pow _ _ (by omega), enumerates_tauOf hE hε (by omega) hs0 hs, fun n φ h3 hne => ?_⟩
  have h3' : SatK.IsKCNF 3 φ := ⟨h3.1, h3.2⟩
  refine ⟨C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ * 2 ^ (C₀ * (n / 2 ^ s)), ?_, time_le_poly h3' (by omega) hε hs⟩
  rw [hL]
  exact hM 3 n s φ (by norm_num) hs0 h3' hne
end Enumerate
