-- Prove2me | solution 1 for CoffmanMitrani1980.Region.priority_vector_unique_solution_eq5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:40:34.522886+00:00
-- url     : https://prove2.me/submissions/d3e13d64-5c24-4659-a995-1c6ab6fcd9ef

import Mathlib
import Definitions.Def_CoffmanMitrani1980_Region_Model

set_option autoImplicit false

open Finset

namespace CM80Eq5Aux

open CoffmanMitrani1980.Region

lemma topSet_zero {M : ℕ} (π : Equiv.Perm (Fin M)) : topSet π 0 = ∅ := by
  unfold topSet
  simp

lemma topSet_succ {M : ℕ} (π : Equiv.Perm (Fin M)) (k : ℕ) (hk : k < M) :
    topSet π (k + 1) = insert (π ⟨k, hk⟩) (topSet π k) := by
  unfold topSet
  ext x
  simp only [mem_image, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact Or.inr ⟨j, h, rfl⟩
    · left; congr 1; exact Fin.ext h
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
    · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩

lemma not_mem_topSet {M : ℕ} (π : Equiv.Perm (Fin M)) (k : ℕ) (hk : k < M) :
    π ⟨k, hk⟩ ∉ topSet π k := by
  unfold topSet
  simp only [mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
  intro j hj h
  have := π.injective h
  rw [this] at hj
  exact lt_irrefl _ hj

lemma sum_topSet_succ {M : ℕ} (π : Equiv.Perm (Fin M)) (k : ℕ) (hk : k < M)
    (g : Fin M → ℝ) :
    ∑ i ∈ topSet π (k + 1), g i = g (π ⟨k, hk⟩) + ∑ i ∈ topSet π k, g i := by
  rw [topSet_succ π k hk, sum_insert (not_mem_topSet π k hk)]

lemma f_empty {M : ℕ} (p : Params M) : p.f ∅ = 0 := by
  unfold Params.f
  simp

end CM80Eq5Aux

open CoffmanMitrani1980.Region in
theorem solution {M : ℕ} (p : Params M) (π : Equiv.Perm (Fin M))
    (W : Fin M → ℝ) :
    (∀ k : Fin M, ∑ i ∈ topSet π ((k : ℕ) + 1), p.rho i * W i = p.f (topSet π ((k : ℕ) + 1))) ↔
      W = p.prioVec π := by
  have hrho : ∀ i, 0 < p.rho i := fun i => div_pos (p.lam_pos i) (p.mu_pos i)
  constructor
  · intro h
    -- s r = f (T r) for all r ≤ M
    have hs : ∀ r : ℕ, r ≤ M →
        ∑ i ∈ topSet π r, p.rho i * W i = p.f (topSet π r) := by
      intro r hr
      rcases r with _ | m
      · rw [CM80Eq5Aux.topSet_zero, CM80Eq5Aux.f_empty, sum_empty]
      · exact h ⟨m, by omega⟩
    funext i
    set r := π.symm i with hr
    have hri : π r = i := by simp [hr]
    have h1 := h r
    rw [CM80Eq5Aux.sum_topSet_succ π r.val r.isLt] at h1
    have hfin : (⟨r.val, r.isLt⟩ : Fin M) = r := Fin.ext rfl
    rw [hfin, hri, hs r.val (le_of_lt r.isLt)] at h1
    unfold Params.prioVec
    rw [← hr]
    rw [eq_div_iff (ne_of_gt (hrho i))]
    linarith
  · rintro rfl k
    have key : ∀ n : ℕ, n ≤ M →
        ∑ i ∈ topSet π n, p.rho i * p.prioVec π i = p.f (topSet π n) := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [CM80Eq5Aux.topSet_zero, CM80Eq5Aux.f_empty, sum_empty]
      | succ m ih =>
        intro hm
        have hmM : m < M := by omega
        rw [CM80Eq5Aux.sum_topSet_succ π m hmM, ih (le_of_lt hmM)]
        unfold Params.prioVec
        rw [Equiv.symm_apply_apply, mul_div_cancel₀ _ (ne_of_gt (hrho _))]
        ring
    exact key _ (by omega)
