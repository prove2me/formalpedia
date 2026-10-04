-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.mconvex_descent_direction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:31:05.943513+00:00
-- url     : https://prove2.me/submissions/8b955709-2d1d-4a3a-a5ce-777911516577

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open DiscreteConvex.MConvexFunctionsB

namespace Descent

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_pos {x y : V → ℤ} {u : V} : u ∈ SuppPos x y ↔ y u < x u := by simp [SuppPos]
theorem mem_neg {x y : V → ℤ} {v : V} : v ∈ SuppNeg x y ↔ x v < y v := by simp [SuppNeg]

/-- The double minimum appearing in the statement. -/
noncomputable def MD (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) : WithTop ℝ :=
  (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
    f (fun w => x w - CharVec u w + CharVec v w)))

theorem md_le (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) (u v : V) (hu : u ∈ SuppPos x y)
    (hv : v ∈ SuppNeg x y) : MD f x y ≤ f (fun w => x w - CharVec u w + CharVec v w) :=
  (Finset.inf_le hu).trans (Finset.inf_le hv)

def d1 (x y : V → ℤ) : ℤ := ∑ w, |x w - y w|

theorem d1_nonneg (x y : V → ℤ) : 0 ≤ d1 x y := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem step_dist (x y : V → ℤ) (u v : V) (hu : y u < x u) (hv : x v < y v) :
    d1 x (fun w => y w + CharVec u w - CharVec v w) < d1 x y := by
  have huv : u ≠ v := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    simp only [CharVec]
    by_cases h1 : w = u
    · subst h1
      simp only [if_true, if_neg huv]
      rcases abs_cases (x w - y w) with ⟨h, _⟩ | ⟨h, _⟩ <;>
        rcases abs_cases (x w - (y w + 1 - 0)) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
    · by_cases h2 : w = v
      · subst h2
        simp only [if_neg h1, if_true]
        rcases abs_cases (x w - y w) with ⟨h, _⟩ | ⟨h, _⟩ <;>
          rcases abs_cases (x w - (y w + 0 - 1)) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
      · simp [h1, h2]
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [CharVec, if_true, if_neg huv]
    rcases abs_cases (x u - y u) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rcases abs_cases (x u - (y u + 1 - 0)) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega

theorem shift_pos {x y : V → ℤ} {u v u' : V} (hv : x v < y v)
    (h : u' ∈ SuppPos x (fun w => y w + CharVec u w - CharVec v w)) : u' ∈ SuppPos x y := by
  rw [mem_pos] at h ⊢
  simp only [CharVec] at h
  by_cases h1 : u' = u <;> by_cases h2 : u' = v <;> simp [h1, h2] at h <;> subst_vars <;> omega

theorem shift_neg {x y : V → ℤ} {u v v' : V} (hu : y u < x u)
    (h : v' ∈ SuppNeg x (fun w => y w + CharVec u w - CharVec v w)) : v' ∈ SuppNeg x y := by
  rw [mem_neg] at h ⊢
  simp only [CharVec] at h
  by_cases h1 : v' = u <;> by_cases h2 : v' = v <;> simp [h1, h2] at h <;> subst_vars <;> omega

theorem pos_nonempty (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x y : V → ℤ)
    (hx : x ∈ DomZ f) (hy : y ∈ DomZ f) (hxy : x ≠ y) : ∃ u, u ∈ SuppPos x y := by
  by_contra hno
  push Not at hno
  have hle : ∀ w, x w ≤ y w := fun w => by
    by_contra h; push Not at h; exact hno w (mem_pos.mpr h)
  obtain ⟨w, hw⟩ : ∃ w, x w ≠ y w := by
    by_contra h; push Not at h; exact hxy (funext h)
  have hwlt : x w < y w := lt_of_le_of_ne (hle w) hw
  obtain ⟨v, hv, -⟩ := hf y hy x hx w (mem_pos.mpr hwlt)
  rw [mem_neg] at hv
  exact absurd (hle v) (not_le.mpr hv)

theorem main (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x : V → ℤ) (hx : x ∈ DomZ f) :
    ∀ n : ℕ, ∀ y ∈ DomZ f, d1 x y < n → f x > f y → f x > MD f x y := by
  intro n
  induction n with
  | zero => intro y _ hd; exact absurd hd (by have := d1_nonneg x y; push_cast; omega)
  | succ n ih =>
    intro y hy hd hgt
    have hxy : x ≠ y := by rintro rfl; exact lt_irrefl _ hgt
    obtain ⟨u, hu⟩ := pos_nonempty f hf x y hx hy hxy
    obtain ⟨v, hv, hineq⟩ := hf x hx y hy u hu
    by_cases hlt : f (fun w => x w - CharVec u w + CharVec v w) < f x
    · exact lt_of_le_of_lt (md_le f x y u v hu hv) hlt
    · push Not at hlt
      set y' : V → ℤ := fun w => y w + CharVec u w - CharVec v w with hy'
      have hy'le : f y' ≤ f y := by
        have h1 : f x + f y' ≤ f x + f y :=
          calc f x + f y' ≤ f (fun w => x w - CharVec u w + CharVec v w) + f y' := by gcongr
            _ ≤ f x + f y := hineq
        exact (WithTop.add_le_add_iff_left hx).mp h1
      have hy'lt : f y' < f x := lt_of_le_of_lt hy'le hgt
      have hy'dom : y' ∈ DomZ f := ne_top_of_lt hy'lt
      have hd' : d1 x y' < n := by
        have := step_dist x y u v (mem_pos.mp hu) (mem_neg.mp hv)
        rw [← hy'] at this
        push_cast at hd ⊢; omega
      have ih' := ih y' hy'dom hd' hy'lt
      refine lt_of_le_of_lt ?_ ih'
      refine Finset.le_inf (fun u' hu'' => Finset.le_inf (fun v' hv'' => ?_))
      exact md_le f x y u' v' (shift_pos (mem_neg.mp hv) hu'') (shift_neg (mem_pos.mp hu) hv'')

end Descent

open Descent in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x y : V → ℤ) (hx : x ∈ DomZ f)
    (hy : y ∈ DomZ f) (hgt : f x > f y) :
    f x > (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
      f (fun w => x w - CharVec u w + CharVec v w))) :=
  main f hf x hx ((d1 x y).toNat + 1) y hy (by have := d1_nonneg x y; push_cast; omega) hgt

#print axioms solution
