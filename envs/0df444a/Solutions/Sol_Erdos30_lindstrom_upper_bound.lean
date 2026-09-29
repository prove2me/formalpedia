-- Prove2me | solution 1 for Erdos30.lindstrom_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @markkim
-- created : 2026-09-26T15:22:17.550904+00:00
-- url     : https://prove2.me/submissions/1e06d9e8-ed67-498a-aafd-8337044b1fd5

import Mathlib
import Definitions.Def_Erdos30Basic

/-!
Lindström's bound `h N ≤ √N + N^(1/4) + 1` (Erdős–Turán 1941, Lindström 1969).

Proof: let `a_0 < … < a_{k-1}` be a Sidon subset of `{1, …, N}` and fix `r ≥ 1`.
The `M = Σ_{j<r} (k - j - 1)` differences `a_{i+j+1} - a_i` (`j < r`, `i + j + 1 < k`)
are distinct positive integers, so their sum is at least `M (M + 1) / 2`.
On the other hand the differences of order `j + 1` telescope: their sum is
`Σ_{t ≤ j} (a_{k-j-1+t} - a_t) ≤ (j + 1)(N - 1)`. Hence `M (M+1) ≤ (N-1) r (r+1)`,
i.e. `r (2k - r - 1) ≤ 2 √(N r (r+1))`, and `r = ⌈N^(1/4)⌉` gives the bound.
-/

open Finset

namespace Erdos30

/-- A finite set of positive integers of size `m` has sum at least `1 + 2 + ⋯ + m`. -/
lemma card_mul_succ_le_two_mul_sum (S : Finset ℤ) (hS : ∀ x ∈ S, 1 ≤ x) :
    (S.card : ℤ) * (S.card + 1) ≤ 2 * ∑ x ∈ S, x := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have ha_notin : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => hS x (Finset.mem_insert_of_mem hx)
    have ha1 : 1 ≤ a := hS a (Finset.mem_insert_self a s)
    have hsub : s ⊆ Finset.Icc 1 (a - 1) := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨hs x hx, by have := ha x hx; omega⟩
    have hcard : (s.card : ℤ) ≤ a - 1 := by
      have h1 := Finset.card_le_card hsub
      rw [Int.card_Icc] at h1
      have h2 : (((a - 1 + 1 - 1).toNat : ℕ) : ℤ) = a - 1 := by
        rw [Int.toNat_of_nonneg (by omega)]; ring
      have h3 : ((s.card : ℕ) : ℤ) ≤ (((a - 1 + 1 - 1).toNat : ℕ) : ℤ) := by exact_mod_cast h1
      linarith
    rw [Finset.card_insert_of_notMem ha_notin, Finset.sum_insert ha_notin]
    have := ih hs
    push_cast
    nlinarith

/-- Telescoping: `Σ_{i<m} (f (i+s+1) - f (i+s)) = f (m+s) - f s`. -/
lemma sum_range_sub_shift (f : ℕ → ℤ) (s : ℕ) : ∀ m : ℕ,
    ∑ i ∈ range m, (f (i + s + 1) - f (i + s)) = f (m + s) - f s := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show m + 1 + s = m + s + 1 by ring]
    ring

/-- Sum of the differences of order `s`: `Σ_{i<m} (f (i+s) - f i) = Σ_{t<s} (f (m+t) - f t)`. -/
lemma sum_range_sub_step (f : ℕ → ℤ) (m : ℕ) : ∀ s : ℕ,
    ∑ i ∈ range m, (f (i + s) - f i) = ∑ t ∈ range s, (f (m + t) - f t) := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    have hsplit : ∀ i, f (i + (s + 1)) - f i
        = (f (i + s + 1) - f (i + s)) + (f (i + s) - f i) := by
      intro i; rw [show i + (s + 1) = i + s + 1 by ring]; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ih, Finset.sum_range_succ, sum_range_sub_shift]
    ring

/-- Gauss: `2 Σ_{j<n} j = n (n - 1)`. -/
lemma two_mul_sum_range_id (n : ℕ) : (∑ j ∈ range n, (j : ℤ)) * 2 = (n : ℤ) * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

/-- Lindström's inequality for an arbitrary Sidon subset of `{1, …, N}`. -/
lemma card_le_of_isSidon (N : ℕ) (A : Finset ℕ) (hA : IsSidon (A : Set ℕ))
    (hsub : A ⊆ Finset.Icc 1 N) :
    (A.card : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ ((1 : ℝ) / 4) + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, A.card = k := ⟨_, rfl⟩
  rw [hk]
  set x : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4) with hx
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0 _
  have hx2 : x ^ 2 = Real.sqrt N := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0, Real.sqrt_eq_rpow]
    norm_num
  have hsqrt0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  set r : ℕ := ⌈x⌉₊ with hr
  have hxr : x ≤ r := Nat.le_ceil x
  have hrx : (r : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  -- Trivial case: `k ≤ r < x + 1`.
  by_cases hkr : k ≤ r
  · refine le_of_lt ?_
    calc (k : ℝ) ≤ r := by exact_mod_cast hkr
      _ < x + 1 := hrx
      _ ≤ Real.sqrt N + x + 1 := by linarith
  rw [not_le] at hkr
  -- Main case: `r < k`.
  have hk1 : 1 ≤ k := by omega
  have hN1 : 1 ≤ N := by
    have hA_ne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hA_ne
    have := Finset.mem_Icc.mp (hsub ha)
    omega
  have hxpos : 0 < x := Real.rpow_pos_of_pos (by exact_mod_cast hN1) _
  have hrpos : 0 < r := Nat.ceil_pos.mpr hxpos
  -- The increasing enumeration `g` of `A`.
  obtain ⟨g, hg_mem, hg_lt⟩ : ∃ g : ℕ → ℕ,
      (∀ i, i < k → g i ∈ A) ∧ (∀ i j, i < j → j < k → g i < g j) := by
    refine ⟨fun i => if hi : i < k then A.orderEmbOfFin hk ⟨i, hi⟩ else 0, ?_, ?_⟩
    · intro i hi
      simp only [dif_pos hi]
      exact A.orderEmbOfFin_mem hk ⟨i, hi⟩
    · intro i j hij hj
      have hi : i < k := lt_trans hij hj
      simp only [dif_pos hi, dif_pos hj]
      exact (A.orderEmbOfFin hk).strictMono (Fin.mk_lt_mk.mpr hij)
  have hg_inj : ∀ i j, i < k → j < k → g i = g j → i = j := by
    intro i j hi hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (ne_of_lt (hg_lt i j h hj))
    · exact h
    · exact absurd hij (ne_of_gt (hg_lt j i h hi))
  have hg_bounds : ∀ i, i < k → 1 ≤ g i ∧ g i ≤ N :=
    fun i hi => Finset.mem_Icc.mp (hsub (hg_mem i hi))
  set f : ℕ → ℤ := fun i => (g i : ℤ) with hf
  -- Index set of the differences of order `≤ r`, and the difference map.
  set P : Finset (Σ _ : ℕ, ℕ) := (range r).sigma (fun j => range (k - (j + 1))) with hP
  set D : (Σ _ : ℕ, ℕ) → ℤ := fun p => f (p.2 + (p.1 + 1)) - f p.2 with hD
  have hP_mem : ∀ p ∈ P, p.1 < r ∧ p.2 + (p.1 + 1) < k := by
    intro p hp
    rw [hP, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hp
    omega
  -- The differences are positive.
  have hD_pos : ∀ p ∈ P, 1 ≤ D p := by
    intro p hp
    obtain ⟨_, h2⟩ := hP_mem p hp
    have := hg_lt p.2 (p.2 + (p.1 + 1)) (by omega) h2
    simp only [hD, hf]
    omega
  -- The differences are pairwise distinct (Sidon property).
  have hD_inj : Set.InjOn D (P : Set (Σ _ : ℕ, ℕ)) := by
    rintro ⟨j, i⟩ hp ⟨j', i'⟩ hq hpq
    have hp' := hP_mem _ (Finset.mem_coe.mp hp)
    have hq' := hP_mem _ (Finset.mem_coe.mp hq)
    simp only at hp' hq'
    simp only [hD, hf] at hpq
    have heq : g (i + (j + 1)) + g i' = g (i' + (j' + 1)) + g i := by omega
    have hmem1 := hg_mem _ hp'.2
    have hmem2 := hg_mem i' (by omega)
    have hmem3 := hg_mem _ hq'.2
    have hmem4 := hg_mem i (by omega)
    rcases hA _ (Finset.mem_coe.mpr hmem1) _ (Finset.mem_coe.mpr hmem3)
        _ (Finset.mem_coe.mpr hmem2) _ (Finset.mem_coe.mpr hmem4) heq with
      ⟨h1, h2⟩ | ⟨h1, _⟩
    · have e1 := hg_inj _ _ hp'.2 hq'.2 h1
      have e2 := hg_inj _ _ (by omega) (by omega) h2
      have e3 : j = j' := by omega
      have e4 : i = i' := by omega
      subst e3; subst e4; rfl
    · have := hg_lt i (i + (j + 1)) (by omega) hp'.2
      omega
  -- `2 |P| = r (2k - r - 1)`.
  have hM : ∀ n : ℕ, n ≤ k →
      ((∑ j ∈ range n, (k - (j + 1)) : ℕ) : ℤ) * 2 = (n : ℤ) * (2 * k - n - 1) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have := ih (by omega)
      rw [Finset.sum_range_succ]
      push_cast [Nat.cast_sub (show n + 1 ≤ k from hn)] at this ⊢
      linear_combination this
  have hP_card : (P.card : ℤ) * 2 = (r : ℤ) * (2 * k - r - 1) := by
    rw [hP, Finset.card_sigma]
    simp only [Finset.card_range]
    exact hM r hkr.le
  -- Lower bound on the sum of the differences.
  have hlow : (P.card : ℤ) * (P.card + 1) ≤ 2 * ∑ p ∈ P, D p := by
    have himg := card_mul_succ_le_two_mul_sum (P.image D) (by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      exact hD_pos p hp)
    rw [Finset.card_image_of_injOn hD_inj, Finset.sum_image hD_inj] at himg
    exact himg
  -- Upper bound on the sum of the differences (telescoping).
  have hup : 2 * ∑ p ∈ P, D p ≤ ((N : ℤ) - 1) * (r * (r + 1)) := by
    rw [hP, Finset.sum_sigma]
    have hj : ∀ j ∈ range r,
        ∑ i ∈ range (k - (j + 1)), D ⟨j, i⟩ ≤ ((j : ℤ) + 1) * ((N : ℤ) - 1) := by
      intro j hj
      rw [Finset.mem_range] at hj
      simp only [hD]
      rw [sum_range_sub_step f (k - (j + 1)) (j + 1)]
      calc ∑ t ∈ range (j + 1), (f (k - (j + 1) + t) - f t)
          ≤ ∑ t ∈ range (j + 1), ((N : ℤ) - 1) := by
            apply Finset.sum_le_sum
            intro t ht
            rw [Finset.mem_range] at ht
            have h1 := hg_bounds (k - (j + 1) + t) (by omega)
            have h2 := hg_bounds t (by omega)
            simp only [hf]
            omega
        _ = ((j : ℤ) + 1) * ((N : ℤ) - 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have hsum := Finset.sum_le_sum hj
    have hg2 := two_mul_sum_range_id r
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] at hsum
    have : ((∑ j ∈ range r, (j : ℤ)) + r) * ((N : ℤ) - 1) * 2 = ((N : ℤ) - 1) * (r * (r + 1)) := by
      linear_combination ((N : ℤ) - 1) * hg2
    linarith
  -- Combine: `(r (2k - r - 1))² ≤ 4 N r (r + 1)`.
  have hMnonneg : (0 : ℤ) ≤ P.card := by positivity
  have hrr : (0 : ℤ) ≤ (r : ℤ) * (r + 1) := by positivity
  have hM2 : ((P.card : ℤ) * 2) ^ 2 ≤ 4 * (N : ℤ) * (r * (r + 1)) := by
    nlinarith [hlow, hup, hMnonneg, hrr]
  rw [hP_card] at hM2
  have hM2R : ((r : ℝ) * (2 * k - r - 1)) ^ 2 ≤ 4 * (N : ℝ) * (r * (r + 1)) := by
    exact_mod_cast hM2
  -- Take square roots: `r (2k - r - 1) ≤ √N (2r + 1)`.
  have ht : (0 : ℝ) < 2 * k - r - 1 := by
    have : (r : ℝ) + 1 ≤ k := by exact_mod_cast hkr
    linarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hsq : ((r : ℝ) * (2 * k - r - 1)) ^ 2 ≤ (Real.sqrt N * (2 * r + 1)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hN0]
    nlinarith [hM2R, hN0]
  have hle : (r : ℝ) * (2 * k - r - 1) ≤ Real.sqrt N * (2 * r + 1) := by
    have h1 : 0 ≤ (r : ℝ) * (2 * k - r - 1) := mul_nonneg hrR.le ht.le
    have h2 : 0 ≤ Real.sqrt N * (2 * r + 1) := by positivity
    exact (sq_le_sq₀ h1 h2).mp hsq
  -- Finish: `√N = x² ≤ x r` and `r < x + 1`.
  have hx2r : x ^ 2 ≤ x * r := by nlinarith [hxr, hx0]
  have hr2 : (r : ℝ) * r < r * (x + 1) := mul_lt_mul_of_pos_left hrx hrR
  have key : 2 * (r : ℝ) * k ≤ 2 * r * (Real.sqrt N + x + 1) := by
    nlinarith [hle, hx2, hx2r, hr2]
  exact le_of_mul_le_mul_left key (by linarith)

end Erdos30

/-- Erdős–Turán / Lindström: `h N ≤ √N + N^(1/4) + 1`. -/
theorem solution (N : ℕ) :
    (Erdos30.h N : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ ((1 : ℝ) / 4) + 1 := by
  change ((Erdos30.maxSidonSubsetCard (Finset.Icc 1 N) : ℕ) : ℝ) ≤ _
  unfold Erdos30.maxSidonSubsetCard
  obtain ⟨B, hB, hsup⟩ := Finset.exists_mem_eq_sup
    ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ Erdos30.IsSidon (B : Set ℕ))
    ⟨∅, by simp [Erdos30.IsSidon]⟩ Finset.card
  rw [hsup]
  rw [Finset.mem_filter, Finset.mem_powerset] at hB
  exact Erdos30.card_le_of_isSidon N B hB.2 hB.1
