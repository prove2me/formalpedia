-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctions.Quasi.quasi_m_minimizer_cut
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:59:03.877413+00:00
-- url     : https://prove2.me/submissions/1f99f3fa-b279-4390-9374-d25770b6e8cf

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_SSQMNeq

open DiscreteConvex.MConvexFunctions
open DiscreteConvex.MConvexFunctions.Quasi

namespace QuasiCutCore

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

lemma exists_closest (S : Set (V → ℤ)) (hS : S.Nonempty) (y : V → ℤ) :
    ∃ z ∈ S, ∀ z' ∈ S, dist1 y z ≤ dist1 y z' := by
  classical
  have hex : ∃ n, ∃ z ∈ S, dist1 y z = n := ⟨_, hS.some, hS.some_mem, rfl⟩
  obtain ⟨z, hz, hzn⟩ := Nat.find_spec hex
  refine ⟨z, hz, fun z' hz' => ?_⟩
  rw [hzn]; exact Nat.find_min' hex ⟨z', hz', rfl⟩

lemma cancel (x : V → ℤ) (v : V) : (fun w => x w - CharVec v w + CharVec v w) = x := by
  funext w; ring

lemma charVec_self (v : V) : CharVec v v = 1 := by simp [CharVec]

lemma charVec_ne {u v : V} (h : u ≠ v) : CharVec v u = 0 := by simp [CharVec, h]

lemma mem_pos {x y : V → ℤ} {u : V} (h : y u < x u) : u ∈ SuppPos x y :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

lemma of_mem_neg {x y : V → ℤ} {v : V} (h : v ∈ SuppNeg x y) : x v < y v :=
  (Finset.mem_filter.mp h).2

/-- Local optimality with respect to all exchanges implies global optimality under (SSQM≠). -/
lemma local_global (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f) (x : V → ℤ) (hx : x ∈ DomZ f)
    (hloc : ∀ s t : V, f x ≤ f (fun w => x w - CharVec s w + CharVec t w)) : x ∈ ArgMin f := by
  have main : ∀ n : ℕ, ∀ y : V → ℤ, dist1 x y = n → f x ≤ f y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro y hyn
    by_contra hlt
    rw [not_le] at hlt
    have hy : y ∈ DomZ f := ne_top_of_lt hlt
    by_cases hex : ∃ u, y u < x u
    · obtain ⟨u, hu⟩ := hex
      obtain ⟨v, hv, hor⟩ := hf x hx y hy (ne_of_gt hlt) u (mem_pos hu)
      have hv' := of_mem_neg hv
      have hd := dist1_step x y u v hu hv'
      have hrec := ih (dist1 x (fun w => y w + CharVec u w - CharVec v w)) (by omega) _ rfl
      rcases hor with h1 | h1 | ⟨-, h1⟩
      · exact absurd h1 (not_lt.mpr (hloc u v))
      · exact absurd (lt_of_le_of_lt hrec (lt_trans h1 hlt)) (lt_irrefl _)
      · rw [h1] at hrec; exact absurd hlt (not_lt.mpr hrec)
    · push_neg at hex
      have hxy : x ≠ y := by rintro rfl; exact lt_irrefl _ hlt
      obtain ⟨u, hu⟩ : ∃ u, x u < y u := by
        by_contra hno; push_neg at hno
        exact hxy (funext fun w => le_antisymm (hex w) (hno w))
      obtain ⟨v, hv, -⟩ := hf y hy x hx (ne_of_lt hlt) u (mem_pos hu)
      have := of_mem_neg hv
      linarith [hex v]
  intro y
  exact main _ y rfl

lemma cut1 (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f) (hne : (ArgMin f).Nonempty)
    (x : V → ℤ) (hx : x ∈ DomZ f) (u v : V)
    (h : ∀ s : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
      f (fun w => x w - CharVec s w + CharVec v w)) :
    ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 + CharVec v u := by
  obtain ⟨y, hy⟩ : ∃ y, y = fun w => x w - CharVec u w + CharVec v w := ⟨_, rfl⟩
  rw [← hy] at h
  have hyx : f y ≤ f x := by have := h v; rwa [cancel] at this
  have hyd : y ∈ DomZ f := ne_top_of_le_ne_top hx hyx
  have hyu : y u = x u - 1 + CharVec v u := by
    rw [hy]; show x u - CharVec u u + CharVec v u = _; rw [charVec_self]
  by_contra hcon
  push_neg at hcon
  obtain ⟨z, hz, hmin⟩ := exists_closest (ArgMin f) hne y
  have hzu : y u < z u := by rw [hyu]; exact hcon z hz
  have hzd : z ∈ DomZ f := ne_top_of_le_ne_top hx (hz x)
  by_cases hfe : f z = f y
  · have hyA : y ∈ ArgMin f := fun w => hfe ▸ hz w
    exact lt_irrefl _ (hyu ▸ hcon y hyA)
  · obtain ⟨s, hs, hor⟩ := hf z hzd y hyd hfe u (mem_pos hzu)
    have hs' := of_mem_neg hs
    have hd := dist1_step y z s u hs' hzu
    have e1 : (fun w => z w + CharVec s w - CharVec u w) =
        (fun w => z w - CharVec u w + CharVec s w) := by funext w; ring
    rw [e1] at hd
    have e2 : (fun w => y w + CharVec u w - CharVec s w) =
        (fun w => x w - CharVec s w + CharVec v w) := by funext w; rw [hy]; ring
    rw [e2] at hor
    rcases hor with h1 | h1 | ⟨h1, -⟩
    · exact absurd (hz _) (not_le.mpr h1)
    · exact absurd (h s) (not_le.mpr h1)
    · have hA : (fun w => z w - CharVec u w + CharVec s w) ∈ ArgMin f := fun w => h1 ▸ hz w
      have := hmin _ hA
      omega

lemma cut2 (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f) (hne : (ArgMin f).Nonempty)
    (x : V → ℤ) (hx : x ∈ DomZ f) (u v : V)
    (h : ∀ t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
      f (fun w => x w - CharVec u w + CharVec t w)) :
    ∃ xs ∈ ArgMin f, xs v ≥ x v - CharVec u v + 1 := by
  obtain ⟨y, hy⟩ : ∃ y, y = fun w => x w - CharVec u w + CharVec v w := ⟨_, rfl⟩
  rw [← hy] at h
  have hyx : f y ≤ f x := by have := h u; rwa [cancel] at this
  have hyd : y ∈ DomZ f := ne_top_of_le_ne_top hx hyx
  have hyv : y v = x v - CharVec u v + 1 := by
    rw [hy]; show x v - CharVec u v + CharVec v v = _; rw [charVec_self]
  by_contra hcon
  push_neg at hcon
  obtain ⟨z, hz, hmin⟩ := exists_closest (ArgMin f) hne y
  have hzv : z v < y v := by rw [hyv]; exact hcon z hz
  have hzd : z ∈ DomZ f := ne_top_of_le_ne_top hx (hz x)
  by_cases hfe : f y = f z
  · have hyA : y ∈ ArgMin f := fun w => hfe ▸ hz w
    exact lt_irrefl _ (hyv ▸ hcon y hyA)
  · obtain ⟨t, ht, hor⟩ := hf y hyd z hzd hfe v (mem_pos hzv)
    have ht' := of_mem_neg ht
    have hd := dist1_step y z v t hzv ht'
    have e2 : (fun w => y w - CharVec v w + CharVec t w) =
        (fun w => x w - CharVec u w + CharVec t w) := by funext w; rw [hy]; ring
    rw [e2] at hor
    rcases hor with h1 | h1 | ⟨-, h1⟩
    · exact absurd (h t) (not_le.mpr h1)
    · exact absurd (hz _) (not_le.mpr h1)
    · have hA : (fun w => z w + CharVec v w - CharVec t w) ∈ ArgMin f := fun w => h1 ▸ hz w
      have := hmin _ hA
      omega

lemma cut3 (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f) (hne : (ArgMin f).Nonempty)
    (x : V → ℤ) (hx : x ∈ DomZ f \ ArgMin f) (u v : V)
    (h : ∀ s t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
      f (fun w => x w - CharVec s w + CharVec t w)) :
    ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 ∧ xs v ≥ x v + 1 := by
  obtain ⟨hxd, hxA⟩ := hx
  by_cases huv : u = v
  · subst huv
    rw [cancel] at h
    exact absurd (local_global f hf x hxd h) hxA
  obtain ⟨y, hy⟩ : ∃ y, y = fun w => x w - CharVec u w + CharVec v w := ⟨_, rfl⟩
  rw [← hy] at h
  have hyd : y ∈ DomZ f := by
    have := h v v; rw [cancel] at this; exact ne_top_of_le_ne_top hxd this
  have hyu : y u = x u - 1 := by
    rw [hy]; show x u - CharVec u u + CharVec v u = _; rw [charVec_self, charVec_ne huv]; ring
  have hyv : y v = x v + 1 := by
    rw [hy]; show x v - CharVec u v + CharVec v v = _
    rw [charVec_self, charVec_ne (Ne.symm huv)]; ring
  by_contra hcon
  push_neg at hcon
  set A := {z | z ∈ ArgMin f ∧ z u ≤ y u} with hA
  have hAne : A.Nonempty := by
    obtain ⟨xs, hxs, hxsu⟩ := cut1 f hf hne x hxd u v (by intro s; rw [← hy]; exact h s v)
    refine ⟨xs, hxs, ?_⟩
    rw [hyu]; rw [charVec_ne huv] at hxsu; linarith
  obtain ⟨z, ⟨hz, hzu⟩, hmin⟩ := exists_closest A hAne y
  have hzv : z v < y v := by
    have := hcon z hz (by linarith); rw [hyv]; exact this
  have hzd : z ∈ DomZ f := ne_top_of_le_ne_top hxd (hz x)
  by_cases hfe : f y = f z
  · have hyA : y ∈ ArgMin f := fun w => hfe ▸ hz w
    have := hcon y hyA (by rw [hyu])
    rw [hyv] at this; exact lt_irrefl _ this
  · obtain ⟨t, ht, hor⟩ := hf y hyd z hzd hfe v (mem_pos hzv)
    have ht' := of_mem_neg ht
    have hd := dist1_step y z v t hzv ht'
    have e2 : (fun w => y w - CharVec v w + CharVec t w) =
        (fun w => x w - CharVec u w + CharVec t w) := by funext w; rw [hy]; ring
    rw [e2] at hor
    rcases hor with h1 | h1 | ⟨-, h1⟩
    · exact absurd (h u t) (not_le.mpr h1)
    · exact absurd (hz _) (not_le.mpr h1)
    · have hmem : (fun w => z w + CharVec v w - CharVec t w) ∈ A := by
        refine ⟨fun w => h1 ▸ hz w, ?_⟩
        show z u + CharVec v u - CharVec t u ≤ y u
        rw [charVec_ne huv]
        have : 0 ≤ CharVec t u := by unfold CharVec; split_ifs <;> norm_num
        linarith
      have := hmin _ hmem
      omega

end QuasiCutCore

open QuasiCutCore in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : SSQMNeq f) (hne : (ArgMin f).Nonempty) :
    (∀ x ∈ DomZ f, ∀ v u : V,
        (∀ s : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec v w)) →
        ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 + CharVec v u) ∧
    (∀ x ∈ DomZ f, ∀ u v : V,
        (∀ t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec u w + CharVec t w)) →
        ∃ xs ∈ ArgMin f, xs v ≥ x v - CharVec u v + 1) ∧
    (∀ x ∈ DomZ f \ ArgMin f, ∀ u v : V,
        (∀ s t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec t w)) →
        ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 ∧ xs v ≥ x v + 1) :=
  ⟨fun x hx v u h => cut1 f hf hne x hx u v h, fun x hx u v h => cut2 f hf hne x hx u v h,
    fun x hx u v h => cut3 f hf hne x hx u v h⟩

#print axioms solution
