-- Prove2me | solution 1 for FuzzyExtractors.EditSketch.construction_6_step_4
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:21:46.407256+00:00
-- url     : https://prove2.me/submissions/c824ae1f-4853-4ea8-9e1f-9a47e9419349

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

open FuzzyExtractors.EditSketch

private theorem bch_injective {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
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


private theorem syn_sq {K : Type} [Field K] [CharP K 2] (s : Finset Kˣ) (i : ℕ) :
    syn (2*i) s = syn i s ^ 2 := by
  classical
  unfold syn
  rw [sum_pow_char]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← pow_mul, Nat.mul_comm]

private theorem syn_diff {K : Type} [Field K] [DecidableEq K] [CharP K 2]
    (w w' : Finset Kˣ) (k : ℕ) : syn k (symmDiff w w') = syn k w' - syn k w := by
  classical
  have hdis : Disjoint (w \ w') (w' \ w) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  have hw := Finset.sum_sdiff (f := fun x : Kˣ => (x : K)^k) (Finset.inter_subset_left (s₁ := w) (s₂ := w'))
  have hw' := Finset.sum_sdiff (f := fun x : Kˣ => (x : K)^k) (Finset.inter_subset_right (s₁ := w) (s₂ := w'))
  simp only [Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right] at hw hw'
  unfold syn
  rw [Finset.symmDiff_def, Finset.sum_union hdis, CharTwo.sub_eq_add]
  have hz := CharTwo.add_self_eq_zero (∑ x ∈ w ∩ w', (x : K)^k)
  linear_combination hw + hw' - hz

theorem solution {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [CharP K 2] (t : ℕ) (w w' v : Finset Kˣ) (hdis : symmDiffDis w w' ≤ t) (hv : v.card ≤ t)
    (hsyn : ∀ j : Fin t,
      syn (2 * (j : ℕ) + 1) v = syn (2 * (j : ℕ) + 1) w' - syn (2 * (j : ℕ) + 1) w) :
    v = symmDiff w w' := by
  have hodd : ∀ j : Fin t, syn (2 * (j : ℕ) + 1) v =
      syn (2 * (j : ℕ) + 1) (symmDiff w w') := by
    intro j
    rw [hsyn, syn_diff]
  apply bch_injective (2*t+1) v (symmDiff w w') (by simpa using hv)
    (by simpa [symmDiffDis] using hdis)
  intro k hk hkt
  have hall : ∀ k : ℕ, 1 ≤ k → k ≤ 2*t →
      syn k v = syn k (symmDiff w w') := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk hkt
      by_cases he : k % 2 = 0
      · have hhalf : 1 ≤ k/2 := by omega
        have hrec := ih (k/2) (by omega) hhalf (by omega)
        have heq : k = 2*(k/2) := by omega
        rw [heq, syn_sq, syn_sq, hrec]
      · have heq : k = 2*(k/2)+1 := by omega
        have hj : k/2 < t := by omega
        rw [heq]
        exact hodd ⟨k/2,hj⟩
  exact hall k hk (by omega)

#print axioms solution
