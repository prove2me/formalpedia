-- Prove2me | solution 1 for FuzzyExtractors.EditSketch.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:20:29.230735+00:00
-- url     : https://prove2.me/submissions/8ee87253-5109-48f6-a97f-e6a943827d32

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

open FuzzyExtractors.EditSketch

theorem solution {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (δ : ℕ) (M M' : Finset Kˣ) (hM : M.card ≤ (δ - 1) / 2) (hM' : M'.card ≤ (δ - 1) / 2)
    (hsyn : ∀ i : ℕ, 1 ≤ i → i ≤ δ - 1 → syn i M = syn i M') :
    M = M' := by
  classical
  let s := M ∪ M'
  let e : Fin s.card ≃ s := (Finset.equivFin s).symm
  let f : Fin s.card → K := fun j => (e j : Kˣ)
  let a : Kˣ → K := fun x => (if x ∈ M then 1 else 0) - (if x ∈ M' then 1 else 0)
  let b : Fin s.card → K := fun j => a (e j) * f j
  have hf : Function.Injective f := by
    intro j k h
    apply e.injective
    apply Subtype.ext
    exact Units.val_injective h
  have hs : s.card ≤ δ - 1 := by
    dsimp [s]
    have := Finset.card_union_le M M'
    omega
  have sum_a (k : ℕ) : (∑ x ∈ s, a x * (x : K) ^ k) = syn k M - syn k M' := by
    simp only [a, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    have h1 : s.filter (fun x => x ∈ M) = M := by ext x; simp [s]
    have h2 : s.filter (fun x => x ∈ M') = M' := by ext x; simp [s]
    rw [h1, h2]
    rfl
  have hb : b = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf
    intro k
    have hh := hsyn (k.val + 1) (by omega) (by omega)
    have hz := sum_a (k.val + 1)
    rw [hh, sub_self] at hz
    calc
      (∑ j : Fin s.card, b j * f j ^ k.val) =
          ∑ j : Fin s.card, a (e j) * (f j) ^ (k.val + 1) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [b]
        rw [pow_succ]
        ring
      _ = ∑ x ∈ s, a x * (x : K) ^ (k.val + 1) := by
        rw [← Finset.sum_coe_sort s]
        exact e.sum_comp (fun x : s => a x * ((x : Kˣ) : K) ^ (k.val + 1))
      _ = 0 := hz
  apply Finset.ext
  intro x
  by_cases hx : x ∈ s
  · have hz := congrFun hb (e.symm ⟨x, hx⟩)
    have ha : a x = 0 := by
      have : a x * (x : K) = 0 := by simpa [b, f] using hz
      exact (mul_eq_zero.mp this).resolve_right x.ne_zero
    by_cases h1 : x ∈ M <;> by_cases h2 : x ∈ M' <;> simp_all [a]
  · have hxm : x ∉ M := fun h => hx (Finset.mem_union_left _ h)
    have hxm' : x ∉ M' := fun h => hx (Finset.mem_union_right _ h)
    simp [hxm, hxm']

#print axioms solution
