-- Prove2me | solution 1 for Enumerate.time_le_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:53:31.802838+00:00
-- url     : https://prove2.me/submissions/9019d935-1c6e-4e46-a23a-e1c4e800191c

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
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_poly_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_SparsificationLemma_Mach_mul_div_le_eps
import Theorems.Thm_SparsificationLemma_Mach_poly_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo SparsificationLemma.Mach Turing
namespace Enumerate
theorem _root_.solution {C₀ C n s : ℕ} {φ : Sat3.CNF n} {ε : ℝ} (h3 : SatK.IsKCNF 3 φ) (hc : C₀ ≤ C) (h0 : 0 < ε) (hs : (C : ℝ) / ε ≤ (2 : ℝ) ^ s) :
    ((C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ * 2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (ε * (n : ℝ)) * (((C₀ * (s + 412) ^ C₀ + 4 * C₀ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C₀ * (s + 412) ^ C₀ + 4 * C₀)) := by
  have hR : ((C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ : ℕ) : ℝ) ≤ ((C₀ * (s + 412) ^ C₀ + 4 * C₀ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C₀ * (s + 412) ^ C₀ + 4 * C₀) := by
    exact_mod_cast poly_le C₀ s h3
  have e1 : ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by
    calc ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) = (2 : ℝ) ^ (((C₀ * (n / 2 ^ s) : ℕ)) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_div_le_eps hc h0 hs)
  calc ((C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ * 2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ)
      = ((C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ : ℕ) : ℝ) * ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) := Nat.cast_mul _ _
    _ ≤ (((C₀ * (s + 412) ^ C₀ + 4 * C₀ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C₀ * (s + 412) ^ C₀ + 4 * C₀)) * (2 : ℝ) ^ (ε * (n : ℝ)) :=
        mul_le_mul hR e1 (by positivity) (by positivity)
    _ = _ := mul_comm _ _
end Enumerate
