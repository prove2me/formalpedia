-- Prove2me | solution 1 for ClauseBound.Boson.sum_abs_aFam_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:46:42.257551+00:00
-- url     : https://prove2.me/submissions/88ec23b5-28e0-443f-91d0-941c3aceec40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual
import Theorems.Thm_ClauseBound_Boson_Dual_sum_range_eq_list
import Theorems.Thm_ClauseBound_Boson_Dual_sum_map_flatMap

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
namespace ClauseBound.Boson
theorem _root_.solution (μ : List ℕ) : ((aFam μ).map fun c => |c.1|).sum ≤ 2 ^ μ.sum := by
  induction μ with
  | nil => simp [aFam]
  | cons n μ ih =>
    have h1 : ((yl n).map fun cj => |cj.1|).sum ≤ 2 ^ n := by
      unfold yl
      rw [List.map_map, ← Dual.sum_range_eq_list]
      have h2 : ∀ i ∈ range n, ((fun cj : ℤ × ℕ => |cj.1|) ∘ fun i => ((-1) ^ (n - 1) * (n.choose (i + 1) : ℤ), i + 1)) i = (n.choose (i + 1) : ℤ) := by
        intro i _
        simp [abs_mul]
      rw [sum_congr rfl h2]
      have h3 := Nat.sum_range_choose n
      rw [sum_range_succ'] at h3
      have h4 : ∑ i ∈ range n, n.choose (i + 1) ≤ 2 ^ n := by omega
      exact_mod_cast h4
    have h0 : 0 ≤ ((aFam μ).map fun c => |c.1|).sum := List.sum_nonneg fun x hx => by
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hx
      exact abs_nonneg _
    rw [aFam, Dual.sum_map_flatMap]
    have h5 : ∀ cj : ℤ × ℕ, (((aFam μ).map fun cL => (cj.1 * cL.1, cj.2 :: cL.2)).map fun c : ℤ × List ℕ => |c.1|).sum
        = |cj.1| * ((aFam μ).map fun c => |c.1|).sum := by
      intro cj
      rw [List.map_map, ← List.sum_map_mul_left]
      exact congrArg List.sum (List.map_congr_left fun c _ => abs_mul _ _)
    simp only [h5]
    rw [List.sum_map_mul_right, List.sum_cons, pow_add]
    exact mul_le_mul h1 ih h0 (by positivity)
end ClauseBound.Boson
