-- Prove2me | solution 1 for Enumerate.enumerates_tauOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:45.411996+00:00
-- url     : https://prove2.me/submissions/180908f9-c64c-4516-ab3d-ab333d6facd6

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
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_UniformInK_Leaves_tauOf_worksU
import Theorems.Thm_UniformInK_stParU
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo SparsificationLemma.Mach Turing
namespace Enumerate
theorem _root_.solution (hE : StEnumeratesTau) {ε : ℝ} {C s : ℕ} (h0 : 0 < ε) (hC : 1 ≤ C) (hs0 : s0U 3 ≤ s) (hs : (C : ℝ) / ε ≤ (2 : ℝ) ^ s) :
    Enumerates ε (tauOf s ^ 6) (tauOf s) := by
  have hτ : 8 * 3 ≤ tauOf s := ((stParU 3 s (by norm_num)).2 hs0).2
  have hw := Leaves.tauOf_worksU (k := 3) (s := s) (by norm_num) hs0
  rw [Nat.cast_ofNat] at hw
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have h2 : (C : ℝ) ≤ (2 : ℝ) ^ s * ε := (div_le_iff₀ h0).1 hs
  have h3 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have h4 : (1 : ℝ) / 2 ^ s ≤ ε := by
    rw [div_le_iff₀ hp]
    linarith
  exact hE (tauOf s) ε (by omega) (hw.trans h4)
end Enumerate
