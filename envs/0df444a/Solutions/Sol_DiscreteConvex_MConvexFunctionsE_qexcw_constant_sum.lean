-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.qexcw_constant_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:11:26.144554+00:00
-- url     : https://prove2.me/submissions/fdcb27ce-f8dd-41d3-9c15-3c5560c7dc1c

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw

set_option autoImplicit false

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise

theorem qexcw_cs_charvec_sum {V : Type*} [Fintype V] [DecidableEq V] (u : V) :
    ∑ w, CharVec u w = 1 := by
  unfold CharVec
  simp

theorem qexcw_cs_dist_lt {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) (u v : V)
    (hu : y u < x u) (hv : x v < y v) :
    ∑ w, (x w - CharVec u w + CharVec v w - y w).natAbs < ∑ w, (x w - y w).natAbs := by
  have huv : u ≠ v := by
    rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    unfold CharVec
    by_cases h1 : w = u
    · subst h1
      simp [huv]
      omega
    · by_cases h2 : w = v
      · subst h2
        simp [h1]
        omega
      · simp [h1, h2]
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    unfold CharVec
    simp [huv]
    omega

end DiscreteConvex.MConvexFunctionsE

open Classical in
open scoped Pointwise in
open DiscreteConvex.MConvexFunctionsE in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) (hB : QEXCw B) :
    ∀ x ∈ B, ∀ y ∈ B, ∑ v, x v = ∑ v, y v := by
  suffices H : ∀ n : ℕ, ∀ x ∈ B, ∀ y ∈ B, ∑ w, (x w - y w).natAbs = n →
      ∑ v, x v = ∑ v, y v by
    intro x hx y hy
    exact H _ x hx y hy rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx y hy hn
    by_cases hxy : x = y
    · rw [hxy]
    obtain ⟨u, hu, v, hv, h⟩ := hB x hx y hy hxy
    simp only [SuppPos, SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    have hlt := qexcw_cs_dist_lt x y u v hu hv
    rcases h with h | h
    · have e := ih _ (hn ▸ hlt) _ h y hy rfl
      have : ∑ w, (x w - CharVec u w + CharVec v w) = ∑ w, x w := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, qexcw_cs_charvec_sum,
          qexcw_cs_charvec_sum]
        ring
      rw [← this, e]
    · have hlt' : ∑ w, (x w - (y w + CharVec u w - CharVec v w)).natAbs < n := by
        rw [← hn]
        refine lt_of_eq_of_lt ?_ hlt
        refine Finset.sum_congr rfl (fun w _ => ?_)
        congr 1
        ring
      have e := ih _ hlt' x hx _ h rfl
      have : ∑ w, (y w + CharVec u w - CharVec v w) = ∑ w, y w := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, qexcw_cs_charvec_sum,
          qexcw_cs_charvec_sum]
        ring
      rw [e, this]
