-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsC.mconvex_satisfies_gs
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:13:55.852516+00:00
-- url     : https://prove2.me/submissions/435afe34-08eb-4a4b-877b-38b23a8149d7

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MGS

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.MConvexFunctionsC

namespace GSCex

abbrev inB (x : Bool → ℤ) : Prop := x true + x false = 1 ∧ 0 ≤ x true ∧ x true ≤ 1

/-- The indicator (value `0`) of `{(1,0), (0,1)}`: an M-convex function. -/
noncomputable def f (x : Bool → ℤ) : WithTop ℝ := if inB x then ((0 : ℝ) : WithTop ℝ) else ⊤

theorem f_in {x : Bool → ℤ} (h : inB x) : f x = ((0 : ℝ) : WithTop ℝ) := by
  simp only [f]; rw [if_pos h]

theorem dom_of {x : Bool → ℤ} (h : f x ≠ ⊤) : inB x := by
  by_contra h'; apply h; simp only [f]; rw [if_neg h']

theorem f_exc : MExchangeAxiom f := by
  intro x hx y hy u hu
  obtain ⟨a1, a2, a3⟩ := dom_of hx
  obtain ⟨b1, b2, b3⟩ := dom_of hy
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  refine ⟨!u, ?_, ?_⟩
  · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
    cases u <;> simp only [Bool.not_true, Bool.not_false] <;> omega
  · rw [f_in ⟨a1, a2, a3⟩, f_in ⟨b1, b2, b3⟩,
      f_in (by cases u <;> refine ⟨?_, ?_, ?_⟩ <;> simp [CharVec] <;> omega),
      f_in (by cases u <;> refine ⟨?_, ?_, ?_⟩ <;> simp [CharVec] <;> omega)]

theorem not_gs : ¬ MGS f := by
  intro h
  let x : Bool → ℤ := fun b => if b then 1 else 0
  let z : Bool → ℤ := fun b => if b then 0 else 1
  let q : Bool → ℝ := fun b => if b then 0 else 1
  have hx : x ∈ ArgMinOn (LinearWeight f (fun _ => 0)) := by
    intro y
    simp only [LinearWeight, zero_mul, Finset.sum_const_zero, neg_zero, WithTop.coe_zero, add_zero]
    rw [f_in (x := x) (by refine ⟨?_, ?_, ?_⟩ <;> simp [x])]
    by_cases hy : inB y
    · rw [f_in hy]
    · simp only [f]; rw [if_neg hy]; exact le_top
  have hz : z ∈ ArgMinOn (LinearWeight f q) := by
    intro y
    simp only [LinearWeight]
    rw [f_in (x := z) (by refine ⟨?_, ?_, ?_⟩ <;> simp [z])]
    by_cases hy : inB y
    · rw [f_in hy]
      simp only [Fintype.sum_bool, q, z, if_true, if_false, Bool.false_eq_true]
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      push_cast
      have : y false ≤ 1 := by omega
      have : (y false : ℝ) ≤ 1 := by exact_mod_cast this
      linarith
    · simp only [f]; rw [if_neg hy]; simp
  obtain ⟨y, hy, hge⟩ := h (fun _ => 0) q (fun v => by cases v <;> simp [q]) x hx ⟨z, hz⟩
  have h1 := hge true (by simp [q])
  -- `y` is a minimizer of `f[q]`, so `y = (0,1)`
  have hle := hy z
  simp only [LinearWeight] at hle
  rw [f_in (x := z) (by refine ⟨?_, ?_, ?_⟩ <;> simp [z])] at hle
  have hyB : inB y := by
    by_contra hyB
    have : f y = ⊤ := by simp only [f]; rw [if_neg hyB]
    rw [this, top_add, ← WithTop.coe_add] at hle
    exact WithTop.coe_ne_top (top_le_iff.mp hle)
  rw [f_in hyB] at hle
  simp only [Fintype.sum_bool, q, z, if_true, if_false, Bool.false_eq_true] at hle
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
  push_cast at hle
  have hyf : (1 : ℝ) ≤ y false := by linarith
  have : (1 : ℤ) ≤ y false := by exact_mod_cast hyf
  simp only [x] at h1
  obtain ⟨b1, b2, b3⟩ := hyB
  simp at h1
  omega

end GSCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f), MGS f) := by
  intro h
  exact GSCex.not_gs (h GSCex.f GSCex.f_exc)

#print axioms solution
