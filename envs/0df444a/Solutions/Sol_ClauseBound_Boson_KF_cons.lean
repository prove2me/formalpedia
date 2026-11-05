-- Prove2me | solution 1 for ClauseBound.Boson.KF_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:52:45.987212+00:00
-- url     : https://prove2.me/submissions/bdb9892b-0563-4e6e-8b58-e888aceda289

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_KF
import Theorems.Thm_ClauseBound_Boson_Dual_sum_map_flatMap

section
namespace ClauseBound.Boson
open Finset
private theorem sum_map_flatMap {α β : Type} (A : List α) (f : α → List β) (φ : β → ℤ) :
    ((A.flatMap f).map φ).sum = (A.map fun x => ((f x).map φ).sum).sum := by
  induction A with
  | nil => rfl
  | cons x A ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]
private theorem sum_map_range (f : ℕ → ℤ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp
private theorem sum_Icc_one (f : ℕ → ℤ) (n : ℕ) : ∑ j ∈ Icc 1 n, f j = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]
private theorem nop_add_smul (n : ℕ) (c : ℤ) (F G : ℤ → Ker) (r : ℤ) (π σ : Multiset ℕ) :
    nop n (fun ρ π σ => c * F ρ π σ + G ρ π σ) r π σ = c * nop n F r π σ + nop n G r π σ := by
  have h1 : ∑ l ∈ π.toFinset, bet n l * cre l (fun π σ => c * F (r - l) π σ + G (r - l) π σ) π σ =
      c * ∑ l ∈ π.toFinset, bet n l * cre l (F (r - l)) π σ + ∑ l ∈ π.toFinset, bet n l * cre l (G (r - l)) π σ := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    simp only [cre]
    split_ifs <;> ring
  have h2 : ∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (fun π σ => c * F (r + k) π σ + G (r + k) π σ) k π σ =
      c * ∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ + ∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (G (r + k)) k π σ := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [ann]
    ring
  simp only [nop]
  rw [h1, h2]
  ring
private theorem nop_zero (n : ℕ) (r : ℤ) (π σ : Multiset ℕ) : nop n (fun _ _ _ => 0) r π σ = 0 := by
  simp [nop, cre, ann]
private theorem nop_list_sum {α : Type} (n : ℕ) (A : List α) (c : α → ℤ) (G : α → ℤ → Ker) (r : ℤ) (π σ : Multiset ℕ) :
    nop n (fun ρ π σ => (A.map fun x => c x * G x ρ π σ).sum) r π σ = (A.map fun x => c x * nop n (G x) r π σ).sum := by
  induction A with
  | nil => exact nop_zero n r π σ
  | cons x A ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [nop_add_smul n (c x) (G x) (fun ρ π σ => (A.map fun x => c x * G x ρ π σ).sum), ih]
private theorem KF_eq (μ : List ℕ) (w : ℕ) :
    KF μ w = fun ρ π σ => ((aFam μ).map fun c => (if c.2.sum = w then c.1 else 0) * op c.2 ρ π σ).sum := by
  funext ρ π σ
  refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
  split_ifs <;> simp
end ClauseBound.Boson
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
namespace ClauseBound.Boson
theorem _root_.solution (n : ℕ) (μ : List ℕ) (w : ℕ) (r : ℤ) (π σ : Multiset ℕ) :
    KF (n :: μ) w r π σ =
      ∑ j ∈ Icc 1 n, if j ≤ w then (-1) ^ (n - 1) * (n.choose j : ℤ) * nop j (KF μ (w - j)) r π σ else 0 := by
  rw [sum_Icc_one, ← sum_map_range, KF, aFam, sum_map_flatMap, yl, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, List.map_map]
  rw [KF_eq μ (w - (i + 1)), nop_list_sum]
  split_ifs with hw
  · rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
    simp only [Function.comp_apply, op]
    have e : ((i + 1) :: c.2).sum = i + 1 + c.2.sum := List.sum_cons
    by_cases hc : c.2.sum = w - (i + 1)
    · rw [if_pos hc, if_pos (by omega)]; ring
    · rw [if_neg hc, if_neg (by omega)]; ring
  · refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    simp only [Function.comp_apply]
    have e : ((i + 1) :: c.2).sum = i + 1 + c.2.sum := List.sum_cons
    rw [if_neg (by omega)]
end ClauseBound.Boson
