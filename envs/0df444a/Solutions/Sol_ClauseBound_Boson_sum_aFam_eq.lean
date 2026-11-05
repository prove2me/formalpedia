-- Prove2me | solution 1 for ClauseBound.Boson.sum_aFam_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:54:50.780363+00:00
-- url     : https://prove2.me/submissions/85bb5a37-e077-4b62-abca-cf46591cad11

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_KF
section
namespace ClauseBound.Boson
open Finset
private theorem sum_mul_sum_map {α : Type} (s : Finset ℕ) (g : ℕ → ℤ) (A : List α) (f : ℕ → α → ℤ) :
    ∑ w ∈ s, g w * (A.map (f w)).sum = (A.map fun c => ∑ w ∈ s, g w * f w c).sum := by
  induction A with
  | nil => simp
  | cons x A ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, sum_add_distrib]
    rw [ih]
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
theorem _root_.solution (μ : List ℕ) (g : ℕ → ℤ) (r : ℤ) (π σ : Multiset ℕ) :
    ((aFam μ).map fun c => c.1 * g c.2.sum * op c.2 r π σ).sum = ∑ w ∈ range (μ.sum + 1), g w * KF μ w r π σ := by
  simp only [KF]
  rw [sum_mul_sum_map (range (μ.sum + 1)) g (aFam μ) fun w c => if c.2.sum = w then c.1 * op c.2 r π σ else 0]
  refine congrArg List.sum (List.map_congr_left fun c hc => ?_)
  have hle := (aFam_shape μ c hc).2.1
  rw [sum_eq_single c.2.sum]
  · rw [if_pos rfl]; ring
  · intro w _ hw
    rw [if_neg (Ne.symm hw), mul_zero]
  · intro h
    exact absurd (mem_range.2 (by omega)) h
end ClauseBound.Boson
