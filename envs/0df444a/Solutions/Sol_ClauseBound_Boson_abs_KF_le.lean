-- Prove2me | solution 1 for ClauseBound.Boson.abs_KF_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:56:52.540955+00:00
-- url     : https://prove2.me/submissions/7aeb4a20-091d-4701-98b6-6e36644b1dd8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_KF
import Theorems.Thm_ClauseBound_Boson_abs_op_le
import Theorems.Thm_ClauseBound_Boson_sum_abs_aFam_le

section
namespace ClauseBound.Boson
open Finset
private theorem abs_sum_map_le {α : Type} (A : List α) (f : α → ℤ) : |(A.map f).sum| ≤ (A.map fun x => |f x|).sum := by
  induction A with
  | nil => simp
  | cons x A ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (by omega)
private theorem sum_map_le {α : Type} (A : List α) (f g : α → ℤ) (h : ∀ x ∈ A, f x ≤ g x) : (A.map f).sum ≤ (A.map g).sum := by
  induction A with
  | nil => simp
  | cons x A ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    omega
private theorem mem_aFam_cons {n : ℕ} {μ : List ℕ} {c : ℤ × List ℕ} (h : c ∈ aFam (n :: μ)) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧ ∃ cL ∈ aFam μ, c.2 = j :: cL.2 := by
  obtain ⟨cj, hcj, hc⟩ := List.mem_flatMap.1 h
  obtain ⟨cL, hcL, rfl⟩ := List.mem_map.1 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hcj
  exact ⟨i + 1, by omega, List.mem_range.1 hi, cL, hcL, rfl⟩
private theorem aFam_shape (μ : List ℕ) : ∀ c ∈ aFam μ, c.2.length = μ.length ∧ c.2.sum ≤ μ.sum ∧ ∀ W, (∀ n ∈ μ, n ≤ W) → ∀ j ∈ c.2, j ≤ W := by
  induction μ with
  | nil =>
    intro c hc
    obtain rfl : c = (1, []) := by simpa [aFam] using hc
    simp
  | cons n μ ih =>
    intro c hc
    obtain ⟨j, -, hj, cL, hcL, e⟩ := mem_aFam_cons hc
    obtain ⟨h1, h2, h3⟩ := ih cL hcL
    rw [e]
    refine ⟨by simp [h1], by simp only [List.sum_cons]; omega, fun W hW i hi => ?_⟩
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hj.trans (hW n (by simp))
    · exact h3 W (fun m hm => hW m (by simp [hm])) i hi
end ClauseBound.Boson
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
namespace ClauseBound.Boson
theorem _root_.solution {W : ℕ} (hW : 1 ≤ W) (μ : List ℕ) (hμ : ∀ n ∈ μ, n ≤ W) (w : ℕ) (r : ℤ) {π σ : Multiset ℕ} (hπ : π.sum ≤ W) (hσ : σ.sum ≤ W) :
    |KF μ w r π σ| ≤ 2 ^ (μ.sum + (4 * W + 1) * μ.length) := by
  have h1 : ∀ c ∈ aFam μ, |if c.2.sum = w then c.1 * op c.2 r π σ else 0| ≤ |c.1| * 2 ^ ((4 * W + 1) * μ.length) := by
    intro c hc
    obtain ⟨hl, -, hp⟩ := aFam_shape μ c hc
    have h2 := abs_op_le hW c.2 (hp W hμ) r hπ hσ
    rw [hl] at h2
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    · rw [abs_zero]
      positivity
  calc |KF μ w r π σ| ≤ ((aFam μ).map fun c => |if c.2.sum = w then c.1 * op c.2 r π σ else 0|).sum := abs_sum_map_le _ _
    _ ≤ ((aFam μ).map fun c => |c.1| * 2 ^ ((4 * W + 1) * μ.length)).sum := sum_map_le _ _ _ h1
    _ = ((aFam μ).map fun c => |c.1|).sum * 2 ^ ((4 * W + 1) * μ.length) := List.sum_map_mul_right ..
    _ ≤ 2 ^ μ.sum * 2 ^ ((4 * W + 1) * μ.length) := mul_le_mul_of_nonneg_right (sum_abs_aFam_le μ) (by positivity)
    _ = 2 ^ (μ.sum + (4 * W + 1) * μ.length) := (pow_add _ _ _).symm
end ClauseBound.Boson
