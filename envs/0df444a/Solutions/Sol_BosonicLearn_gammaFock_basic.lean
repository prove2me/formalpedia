-- Prove2me | solution 1 for BosonicLearn.gammaFock_basic
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:08:37.128206+00:00
-- url     : https://prove2.me/submissions/8cf3419f-f472-40d9-8a76-f19217209269

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix

open BosonicLearn

noncomputable section

/-- The index set of `gammaFock`: matrices `M ∈ ℕ^{n×n}` with row sums `u` and column sums `v`. -/
private def gS {n : ℕ} (u v : Fin n → ℕ) : Finset (Fin n → Fin n → ℕ) :=
  (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n => Finset.range (u i + 1)).filter
    (fun M => (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j)

/-- The box constraint is automatic. -/
private lemma mem_gS {n : ℕ} (u v : Fin n → ℕ) (M : Fin n → Fin n → ℕ) :
    M ∈ gS u v ↔ (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j := by
  unfold gS
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i j => ?_, h⟩
    have h1 : M i j ≤ ∑ j, M i j :=
      Finset.single_le_sum (f := fun j => M i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [h.1 i] at h1
    omega

/-- The combinatorial sum in `gammaFock`. -/
private def gSum {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) : ℂ :=
  ∑ M ∈ gS u v, ∏ i, ∏ j, R i j ^ (M i j) / (Nat.factorial (M i j) : ℂ)

private lemma gammaFock_eq {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock R u v =
      (Real.sqrt ((∏ i, (Nat.factorial (u i) : ℝ)) * ∏ j, (Nat.factorial (v j) : ℝ)) : ℂ) *
        gSum R u v := rfl

/-- No matrix has row sums `u` and column sums `v` unless the totals agree. -/
private lemma gS_eq_empty {n : ℕ} (u v : Fin n → ℕ) (h : ∑ i, u i ≠ ∑ i, v i) : gS u v = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro M hM
  rw [mem_gS] at hM
  apply h
  calc ∑ i, u i = ∑ i, ∑ j, M i j := Finset.sum_congr rfl fun i _ => (hM.1 i).symm
    _ = ∑ j, ∑ i, M i j := Finset.sum_comm
    _ = ∑ j, v j := Finset.sum_congr rfl fun j _ => hM.2 j

/-- Transposition identity for the combinatorial sum. -/
private lemma gSum_conjTranspose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gSum Aᴴ u v = (starRingEnd ℂ) (gSum A v u) := by
  unfold gSum
  rw [map_sum]
  refine Finset.sum_nbij' (fun M i j => M j i) (fun M i j => M j i) ?_ ?_ ?_ ?_ ?_
  · intro M hM
    rw [mem_gS] at hM ⊢
    exact ⟨hM.2, hM.1⟩
  · intro M hM
    rw [mem_gS] at hM ⊢
    exact ⟨hM.2, hM.1⟩
  · intro M _
    rfl
  · intro M _
    rfl
  · intro M _
    rw [Finset.prod_comm]
    simp only [map_prod, map_div₀, map_pow, map_natCast, Matrix.conjTranspose_apply]
    rfl

/-- With `R = 1`, an off-diagonal nonzero entry of `M` kills the term. -/
private lemma term_one_eq_zero {n : ℕ} (M : Fin n → Fin n → ℕ) (i j : Fin n) (hij : i ≠ j)
    (h : M i j ≠ 0) :
    ∏ i, ∏ j, (1 : Matrix (Fin n) (Fin n) ℂ) i j ^ (M i j) / (Nat.factorial (M i j) : ℂ) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  rw [Matrix.one_apply_ne hij, zero_pow h, zero_div]

/-- A matrix with vanishing off-diagonal entries and row sums `u` is `diag u`. -/
private lemma diag_of_offdiag_zero {n : ℕ} (u : Fin n → ℕ) (M : Fin n → Fin n → ℕ)
    (hrow : ∀ i, ∑ j, M i j = u i) (hoff : ∀ i j, i ≠ j → M i j = 0) (i : Fin n) :
    M i i = u i := by
  rw [← hrow i]
  exact (Finset.sum_eq_single i (fun j _ hji => hoff i j (Ne.symm hji))
    (fun h => absurd (Finset.mem_univ i) h)).symm

private lemma diag_of_offdiag_zero' {n : ℕ} (v : Fin n → ℕ) (M : Fin n → Fin n → ℕ)
    (hcol : ∀ j, ∑ i, M i j = v j) (hoff : ∀ i j, i ≠ j → M i j = 0) (j : Fin n) :
    M j j = v j := by
  rw [← hcol j]
  exact (Finset.sum_eq_single j (fun i _ hij => hoff i j hij)
    (fun h => absurd (Finset.mem_univ j) h)).symm

private lemma gSum_one_ne {n : ℕ} (u v : Fin n → ℕ) (huv : u ≠ v) :
    gSum (1 : Matrix (Fin n) (Fin n) ℂ) u v = 0 := by
  unfold gSum
  refine Finset.sum_eq_zero fun M hM => ?_
  rw [mem_gS] at hM
  by_cases hoff : ∀ i j, i ≠ j → M i j = 0
  · exfalso
    apply huv
    funext i
    rw [← diag_of_offdiag_zero u M hM.1 hoff i, diag_of_offdiag_zero' v M hM.2 hoff i]
  · push Not at hoff
    obtain ⟨i, j, hij, hne⟩ := hoff
    exact term_one_eq_zero M i j hij hne

private lemma gSum_one_self {n : ℕ} (u : Fin n → ℕ) :
    gSum (1 : Matrix (Fin n) (Fin n) ℂ) u u = ∏ i, (1 / (Nat.factorial (u i) : ℂ)) := by
  unfold gSum
  rw [Finset.sum_eq_single (fun i j => if i = j then u i else 0)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro M hM hne
    rw [mem_gS] at hM
    by_cases hoff : ∀ i j, i ≠ j → M i j = 0
    · exfalso
      apply hne
      funext i j
      by_cases hij : i = j
      · subst hij
        simp [diag_of_offdiag_zero u M hM.1 hoff i]
      · simp [hij, hoff i j hij]
    · push Not at hoff
      obtain ⟨i, j, hij, hne'⟩ := hoff
      exact term_one_eq_zero M i j hij hne'
  · intro h
    exfalso
    apply h
    rw [mem_gS]
    constructor
    · intro i
      simp
    · intro j
      simp

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u v : Occupation (Fin n)) :
    (∑ i, u i ≠ ∑ i, v i → gammaFock A u v = 0) ∧
    gammaFock Aᴴ u v = star (gammaFock A v u) ∧
    gammaFock (1 : Matrix (Fin n) (Fin n) ℂ) u v = (if u = v then 1 else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [gammaFock_eq]
    unfold gSum
    rw [gS_eq_empty u v h, Finset.sum_empty, mul_zero]
  · rw [gammaFock_eq, gammaFock_eq, gSum_conjTranspose]
    change _ = (starRingEnd ℂ) _
    rw [map_mul, Complex.conj_ofReal, mul_comm (∏ i, (Nat.factorial (u i) : ℝ))]
  · rw [gammaFock_eq]
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl, gSum_one_self]
      have hpos : (0 : ℝ) ≤ ∏ i, (Nat.factorial (u i) : ℝ) :=
        Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
      rw [Real.sqrt_mul_self hpos]
      push_cast
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      have : ((Nat.factorial (u i) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
    · rw [if_neg huv, gSum_one_ne u v huv, mul_zero]
