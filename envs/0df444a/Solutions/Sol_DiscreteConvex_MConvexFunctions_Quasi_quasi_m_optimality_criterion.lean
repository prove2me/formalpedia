-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctions.Quasi.quasi_m_optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:55:41.292218+00:00
-- url     : https://prove2.me/submissions/f3330081-e9a2-48a8-a65e-87fe9961bfff

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_SSQMNeqW

open DiscreteConvex.MConvexFunctions
open DiscreteConvex.MConvexFunctions.Quasi

namespace QuasiOptCore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `ℓ₁`-distance on `ℤⱽ`, as a natural number. -/
def dist1 (x y : V → ℤ) : ℕ := ∑ w, (x w - y w).natAbs

/-- Exchanging one unit of `y` towards `x` (`u ∈ supp⁺(x-y)`, `v ∈ supp⁻(x-y)`) lowers the
`ℓ₁`-distance by two. -/
lemma dist1_step (x y : V → ℤ) (u v : V) (hu : y u < x u) (hv : x v < y v) :
    dist1 x (fun w => y w + CharVec u w - CharVec v w) + 2 = dist1 x y := by
  have huv : u ≠ v := by rintro rfl; omega
  unfold dist1
  have hpt : ∀ w, |x w - (y w + CharVec u w - CharVec v w)| =
      |x w - y w| - (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
    intro w
    simp only [CharVec]
    by_cases h1 : w = u
    · rw [h1, if_pos rfl, if_neg huv]
      rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]; ring
    · by_cases h2 : w = v
      · rw [h2, if_pos rfl, if_neg (Ne.symm huv)]
        rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]; ring
      · rw [if_neg h1, if_neg h2]; simp
  have hsum : ((∑ w, (x w - (y w + CharVec u w - CharVec v w)).natAbs : ℕ) : ℤ) + 2 =
      ((∑ w, (x w - y w).natAbs : ℕ) : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ u, Finset.sum_ite_eq' Finset.univ v]
    simp only [Finset.mem_univ, if_true]
    ring
  exact_mod_cast hsum

lemma neighbor_ne (x : V → ℤ) (u v : V) (huv : u ≠ v) :
    (fun w => x w - CharVec u w + CharVec v w) ≠ x := by
  intro h
  have := congrFun h u
  dsimp only [CharVec] at this
  rw [if_pos rfl, if_neg huv] at this
  omega

/-- An exchange step that reaches `x` exactly: `y + χu - χv = x` means `y = x - χu + χv`. -/
lemma step_eq (x y : V → ℤ) (u v : V)
    (h : (fun w => y w + CharVec u w - CharVec v w) = x) :
    y = (fun w => x w - CharVec u w + CharVec v w) := by
  funext w
  have := congrFun h w
  omega

end QuasiOptCore

open QuasiOptCore in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ, QMw f → ∀ x ∈ DomZ f,
      (∀ y : V → ℤ, y ≠ x → f x < f y) ↔
        (∀ u v : V, u ≠ v → f x < f (fun w => x w - CharVec u w + CharVec v w))) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, SSQMNeqW f → ∀ x ∈ DomZ f,
      (∀ y, f x ≤ f y) ↔
        (∀ u v : V, f x ≤ f (fun w => x w - CharVec u w + CharVec v w))) := by
  constructor
  · intro f hf x hx
    constructor
    · intro h u v huv
      exact h _ (neighbor_ne x u v huv)
    · intro hloc
      -- strong induction on the distance to `x`
      have main : ∀ n : ℕ, ∀ y : V → ℤ, dist1 x y = n → y ≠ x → f x < f y := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
        intro y hyn hyx
        by_cases hy : f y = ⊤
        · rw [hy]; exact lt_top_iff_ne_top.mpr hx
        obtain ⟨u, hu, v, hv, hor⟩ := hf x hx y hy (fun h => hyx h.symm)
        have hu' : y u < x u := (Finset.mem_filter.mp hu).2
        have hv' : x v < y v := (Finset.mem_filter.mp hv).2
        have huv : u ≠ v := by rintro rfl; omega
        rcases hor with h1 | h1
        · exact absurd h1 (not_le.mpr (hloc u v huv))
        · obtain ⟨y', hy'⟩ : ∃ y', y' = fun w => y w + CharVec u w - CharVec v w := ⟨_, rfl⟩
          rw [← hy'] at h1
          by_cases hyx' : y' = x
          · rw [hy'] at hyx'
            rw [step_eq x y u v hyx']
            exact hloc u v huv
          · have hd := dist1_step x y u v hu' hv'
            rw [← hy'] at hd
            exact lt_of_lt_of_le (ih (dist1 x y') (by omega) y' rfl hyx') h1
      intro y hyx
      exact main _ y rfl hyx
  · intro f hf x hx
    constructor
    · intro h u v; exact h _
    · intro hloc
      have main : ∀ n : ℕ, ∀ y : V → ℤ, dist1 x y = n → f x ≤ f y := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
        intro y hyn
        by_contra hlt
        rw [not_le] at hlt
        have hy : y ∈ DomZ f := ne_top_of_lt hlt
        obtain ⟨u, hu, v, hv, hor⟩ := hf x hx y hy (ne_of_gt hlt)
        have hu' : y u < x u := (Finset.mem_filter.mp hu).2
        have hv' : x v < y v := (Finset.mem_filter.mp hv).2
        obtain ⟨y', hy'⟩ : ∃ y', y' = fun w => y w + CharVec u w - CharVec v w := ⟨_, rfl⟩
        rw [← hy'] at hor
        have hd := dist1_step x y u v hu' hv'
        rw [← hy'] at hd
        have hrec : f x ≤ f y' := ih (dist1 x y') (by omega) y' rfl
        rcases hor with h1 | h1 | ⟨-, h1⟩
        · exact absurd h1 (not_lt.mpr (hloc u v))
        · exact absurd (lt_of_le_of_lt hrec (lt_trans h1 hlt)) (lt_irrefl _)
        · rw [h1] at hrec
          exact absurd hlt (not_lt.mpr hrec)
      intro y
      exact main _ y rfl

#print axioms solution
