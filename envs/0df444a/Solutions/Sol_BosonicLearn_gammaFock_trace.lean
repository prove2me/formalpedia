-- Prove2me | solution 1 for BosonicLearn.gammaFock_trace
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:15:00.791602+00:00
-- url     : https://prove2.me/submissions/3c71ba88-1694-4ec4-b378-f5ce5ae71a27

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

/-- For diagonal `R`, an off-diagonal nonzero entry of `M` kills the term. -/
private lemma term_diagonal_eq_zero {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (h : M i j ≠ 0) :
    ∏ i, ∏ j, (Matrix.diagonal c) i j ^ (M i j) / (Nat.factorial (M i j) : ℂ) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  rw [Matrix.diagonal_apply_ne c hij, zero_pow h, zero_div]

/-- A matrix with vanishing off-diagonal entries and row sums `u` is `diag u`. -/
private lemma diag_of_offdiag_zero {n : ℕ} (u : Fin n → ℕ) (M : Fin n → Fin n → ℕ)
    (hrow : ∀ i, ∑ j, M i j = u i) (hoff : ∀ i j, i ≠ j → M i j = 0) (i : Fin n) :
    M i i = u i := by
  rw [← hrow i]
  exact (Finset.sum_eq_single i (fun j _ hji => hoff i j (Ne.symm hji))
    (fun h => absurd (Finset.mem_univ i) h)).symm

private lemma gSum_diagonal_self {n : ℕ} (c : Fin n → ℂ) (u : Fin n → ℕ) :
    gSum (Matrix.diagonal c) u u = ∏ i, (c i ^ u i / (Nat.factorial (u i) : ℂ)) := by
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
      exact term_diagonal_eq_zero c M i j hij hne'
  · intro h
    exfalso
    apply h
    rw [mem_gS]
    constructor
    · intro i
      simp
    · intro j
      simp

/-- Diagonal entries of `Γ(diag c)`. -/
private lemma gammaFock_diagonal_self {n : ℕ} (c : Fin n → ℂ) (u : Fin n → ℕ) :
    gammaFock (Matrix.diagonal c) u u = ∏ i, c i ^ u i := by
  rw [gammaFock_eq, gSum_diagonal_self]
  have hpos : (0 : ℝ) ≤ ∏ i, (Nat.factorial (u i) : ℝ) :=
    Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  rw [Real.sqrt_mul_self hpos]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : ((Nat.factorial (u i) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- A finite product of nonnegative convergent series is the series over `ℕⁿ` of the products. -/
private lemma hasSum_pi_prod_of_nonneg (n : ℕ) : ∀ (f : Fin n → ℕ → ℝ) (a : Fin n → ℝ),
    (∀ i k, 0 ≤ f i k) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun u : Fin n → ℕ => ∏ i, f i (u i)) (∏ i, a i) := by
  induction n with
  | zero =>
    intro f a _ _
    simp
  | succ n ih =>
    intro f a hf0 hf
    have ih' := ih (fun i => f i.succ) (fun i => a i.succ)
      (fun i k => hf0 i.succ k) (fun i => hf i.succ)
    have hsum : Summable (fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)) :=
      Summable.mul_of_nonneg (f := f 0) (g := fun u : Fin n → ℕ => ∏ i : Fin n, f i.succ (u i))
        (hf 0).summable ih'.summable (fun k => hf0 0 k)
        (fun u => Finset.prod_nonneg fun i _ => hf0 i.succ (u i))
    have hmul : HasSum (fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i))
        (a 0 * ∏ i : Fin n, a i.succ) :=
      HasSum.mul (f := f 0) (g := fun u : Fin n → ℕ => ∏ i : Fin n, f i.succ (u i)) (hf 0) ih' hsum
    rw [Fin.prod_univ_succ]
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
    refine hmul.congr_fun fun p => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]

theorem solution {n : ℕ} (d : Fin n → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    HasSum (fun u : Occupation (Fin n) => gammaFock (Matrix.diagonal fun i => (d i : ℂ)) u u)
      (∏ i, ((1 - d i)⁻¹ : ℝ)) := by
  have hreal : HasSum (fun u : Fin n → ℕ => ∏ i, d i ^ u i) (∏ i, (1 - d i)⁻¹) :=
    hasSum_pi_prod_of_nonneg n (fun i k => d i ^ k) (fun i => (1 - d i)⁻¹)
      (fun i k => pow_nonneg (hd0 i) k) (fun i => hasSum_geometric_of_lt_one (hd0 i) (hd1 i))
  have hcomplex := Complex.hasSum_ofReal.mpr hreal
  simp only [Complex.ofReal_prod, Complex.ofReal_pow] at hcomplex
  simpa only [gammaFock_diagonal_self] using hcomplex
