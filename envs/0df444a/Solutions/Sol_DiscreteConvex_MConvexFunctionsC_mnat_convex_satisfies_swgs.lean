-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsC.mnat_convex_satisfies_swgs
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:15:24.867029+00:00
-- url     : https://prove2.me/submissions/e932f1d9-05b5-4e28-ae59-bb8f65f904bb

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatSWGS

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.MConvexFunctionsC

namespace Nat1D

/-- The indicator (value `0`) of `{0, 1} ⊆ ℤ`: an M♮-convex function of one variable. -/
noncomputable def f (x : Unit → ℤ) : WithTop ℝ :=
  if 0 ≤ x () ∧ x () ≤ 1 then ((0 : ℝ) : WithTop ℝ) else ⊤

theorem f_in {x : Unit → ℤ} (h : 0 ≤ x () ∧ x () ≤ 1) : f x = ((0 : ℝ) : WithTop ℝ) := by
  simp only [f]; rw [if_pos h]

theorem f_out {x : Unit → ℤ} (h : ¬ (0 ≤ x () ∧ x () ≤ 1)) : f x = ⊤ := by
  simp only [f]; rw [if_neg h]

theorem dom_lift {z : Option Unit → ℤ} (hz : z ∈ DomZ (LiftedFunction f)) :
    z none = -z (some ()) ∧ 0 ≤ z (some ()) ∧ z (some ()) ≤ 1 := by
  by_contra h
  apply hz
  unfold LiftedFunction
  simp only [Finset.univ_unique, Finset.sum_singleton]
  by_cases h1 : z none = -z (some ())
  · rw [if_pos (by simpa using h1)]
    exact f_out (fun h2 => h ⟨h1, h2⟩)
  · rw [if_neg (by simpa using h1)]

theorem lift_val (z : Option Unit → ℤ) (h1 : z none = -z (some ())) (h2 : 0 ≤ z (some ()))
    (h3 : z (some ()) ≤ 1) : LiftedFunction f z = ((0 : ℝ) : WithTop ℝ) := by
  unfold LiftedFunction
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [if_pos (by simpa using h1)]
  exact f_in ⟨h2, h3⟩

theorem f_mnat : MNaturalConvex f := by
  intro x hx y hy u hu
  obtain ⟨hx1, hx2, hx3⟩ := dom_lift hx
  obtain ⟨hy1, hy2, hy3⟩ := dom_lift hy
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  cases u with
  | none =>
    refine ⟨some (), by simp [SuppNeg]; omega, ?_⟩
    rw [lift_val x hx1 hx2 hx3, lift_val y hy1 hy2 hy3,
      lift_val _ (by simp [CharVec]; omega) (by simp [CharVec]; omega) (by simp [CharVec]; omega),
      lift_val _ (by simp [CharVec]; omega) (by simp [CharVec]; omega) (by simp [CharVec]; omega)]
  | some u =>
    have : u = () := Subsingleton.elim _ _
    subst this
    refine ⟨none, by simp [SuppNeg]; omega, ?_⟩
    rw [lift_val x hx1 hx2 hx3, lift_val y hy1 hy2 hy3,
      lift_val _ (by simp [CharVec]; omega) (by simp [CharVec]; omega) (by simp [CharVec]; omega),
      lift_val _ (by simp [CharVec]; omega) (by simp [CharVec]; omega) (by simp [CharVec]; omega)]

/-- `f[w](x) = f(x) - w x` in one variable. -/
theorem lw (w : Unit → ℝ) (x : Unit → ℤ) :
    LinearWeight f w x = f x + ((-(w () * (x () : ℝ)) : ℝ) : WithTop ℝ) := by
  simp [LinearWeight]

end Nat1D

namespace Nat1D

theorem not_swgs : ¬ MNatSWGS f := by
  intro h
  have hx : (fun _ => (0 : ℤ)) ∈ ArgMinOn (LinearWeight f (fun _ => 0)) := by
    intro y
    rw [lw, lw, f_in (by simp)]
    simp only [zero_mul, neg_zero]
    by_cases hy : 0 ≤ y () ∧ y () ≤ 1
    · rw [f_in hy]
    · rw [f_out hy]; exact le_top
  rcases h (fun _ => 0) _ hx () with hA | ⟨α, hα, y, hy, hyu, -⟩
  · -- at `α = 1` the point `1` is strictly better than `0`
    have := hA 1 zero_le_one (fun _ => 1)
    rw [lw, lw, f_in (by simp), f_in (by simp), ← WithTop.coe_add, ← WithTop.coe_add,
      WithTop.coe_le_coe] at this
    norm_num at this
  · -- the required `y` has `y = -1`, outside the domain
    have hyd : ¬ (0 ≤ y () ∧ y () ≤ 1) := by simp at hyu; omega
    have hle := hy (fun _ => 0)
    rw [lw, lw, f_out hyd, top_add, f_in (by simp), ← WithTop.coe_add] at hle
    exact WithTop.coe_ne_top (top_le_iff.mp hle)

end Nat1D

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MNaturalConvex f), MNatSWGS f) := by
  intro h
  exact Nat1D.not_swgs (h Nat1D.f Nat1D.f_mnat)

#print axioms solution
