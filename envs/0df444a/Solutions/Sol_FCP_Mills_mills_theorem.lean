-- Prove2me | solution 1 for FCP.Mills.mills_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T04:20:21.909769+00:00
-- url     : https://prove2.me/submissions/4c37725a-1d8e-42e8-8182-98ec2a9af53f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FCP_Mills
import Theorems.Thm_FCP_Mills_prime_between_consecutive_cubes

open FCP.Mills

theorem solution : ∃ A : ℝ, 1 < A ∧ IsMills A := by
  obtain ⟨N₀, hN₀⟩ := prime_between_consecutive_cubes
  -- a total "next prime" function
  have hstep : ∀ N : ℕ, ∃ p : ℕ, N₀ ≤ N → p.Prime ∧ N ^ 3 < p ∧ p + 1 < (N + 1) ^ 3 := by
    intro N
    by_cases h : N₀ ≤ N
    · obtain ⟨p, hp⟩ := hN₀ N h
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose g hg using hstep
  obtain ⟨p₀, hp₀N, hp₀⟩ := Nat.exists_infinite_primes N₀
  -- Mills' sequence of primes
  obtain ⟨P, hP0, hPs⟩ : ∃ P : ℕ → ℕ, P 0 = p₀ ∧ ∀ n, P (n + 1) = g (P n) :=
    ⟨fun n => Nat.rec p₀ (fun _ q => g q) n, rfl, fun _ => rfl⟩
  have hPinv : ∀ n, N₀ ≤ P n ∧ (P n).Prime := by
    intro n
    induction n with
    | zero => rw [hP0]; exact ⟨hp₀N, hp₀⟩
    | succ n ih =>
      obtain ⟨h1, h2, -⟩ := hg (P n) ih.1
      rw [hPs]
      refine ⟨?_, h1⟩
      have : P n ≤ P n ^ 3 := Nat.le_self_pow (by norm_num) _
      omega
  have hlow : ∀ n, P n ^ 3 < P (n + 1) := fun n => by
    rw [hPs]; exact (hg (P n) (hPinv n).1).2.1
  have hupp : ∀ n, P (n + 1) + 1 < (P n + 1) ^ 3 := fun n => by
    rw [hPs]; exact (hg (P n) (hPinv n).1).2.2
  -- the two bracketing real sequences
  let u : ℕ → ℝ := fun n => ((P n : ℕ) : ℝ) ^ (((3 ^ n : ℕ) : ℝ)⁻¹)
  let v : ℕ → ℝ := fun n => (((P n : ℕ) : ℝ) + 1) ^ (((3 ^ n : ℕ) : ℝ)⁻¹)
  have h3 : ∀ n : ℕ, (3 ^ n : ℕ) ≠ 0 := fun n => by positivity
  have hu0 : ∀ n, 0 ≤ u n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hv0 : ∀ n, 0 ≤ v n := fun n => Real.rpow_nonneg (by positivity) _
  have hu_pow : ∀ n, u n ^ (3 ^ n) = ((P n : ℕ) : ℝ) := fun n =>
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (h3 n)
  have hv_pow : ∀ n, v n ^ (3 ^ n) = ((P n : ℕ) : ℝ) + 1 := fun n =>
    Real.rpow_inv_natCast_pow (by positivity) (h3 n)
  have hu3 : ∀ n, u n ^ (3 ^ (n + 1)) = ((P n : ℕ) : ℝ) ^ 3 := fun n => by
    rw [pow_succ, pow_mul, hu_pow]
  have hv3 : ∀ n, v n ^ (3 ^ (n + 1)) = (((P n : ℕ) : ℝ) + 1) ^ 3 := fun n => by
    rw [pow_succ, pow_mul, hv_pow]
  have hu_le : ∀ n, u n ≤ u (n + 1) := fun n => by
    refine le_of_pow_le_pow_left₀ (h3 (n + 1)) (hu0 _) ?_
    rw [hu3, hu_pow]
    exact_mod_cast (hlow n).le
  have hv_lt : ∀ n, v (n + 1) < v n := fun n => by
    refine lt_of_pow_lt_pow_left₀ (3 ^ (n + 1)) (hv0 _) ?_
    rw [hv3, hv_pow]
    exact_mod_cast hupp n
  have huv : ∀ n, u n < v n := fun n => by
    refine lt_of_pow_lt_pow_left₀ (3 ^ n) (hv0 _) ?_
    rw [hu_pow, hv_pow]
    linarith
  have hu_mono : Monotone u := monotone_nat_of_le_succ hu_le
  have hv_anti : Antitone v := antitone_nat_of_succ_le fun n => (hv_lt n).le
  have huv' : ∀ m n, u m ≤ v n := fun m n =>
    (hu_mono (le_max_left m n)).trans
      ((huv (max m n)).le.trans (hv_anti (le_max_right m n)))
  have hbdd : BddAbove (Set.range u) := ⟨v 0, by rintro _ ⟨m, rfl⟩; exact huv' m 0⟩
  -- Mills' constant for this sequence
  refine ⟨⨆ m, u m, ?_, ?_⟩
  · have h1 : u 0 ≤ ⨆ m, u m := le_ciSup hbdd 0
    have h2 : u 0 = ((P 0 : ℕ) : ℝ) := by simpa using hu_pow 0
    have h3 : (2 : ℝ) ≤ ((P 0 : ℕ) : ℝ) := by exact_mod_cast (hPinv 0).2.two_le
    linarith
  · intro n _
    have hA_ge : u n ≤ ⨆ m, u m := le_ciSup hbdd n
    have hA_lt : (⨆ m, u m) < v n :=
      lt_of_le_of_lt (ciSup_le fun m => huv' m (n + 1)) (hv_lt n)
    have hA0 : 0 ≤ ⨆ m, u m := (hu0 n).trans hA_ge
    have hfloor : ⌊(⨆ m, u m) ^ (3 ^ n)⌋₊ = P n := by
      rw [Nat.floor_eq_iff (pow_nonneg hA0 _)]
      constructor
      · rw [← hu_pow n]
        exact pow_le_pow_left₀ (hu0 n) hA_ge _
      · rw [← hv_pow n]
        exact pow_lt_pow_left₀ hA_lt hA0 (h3 n)
    rw [hfloor]
    exact (hPinv n).2
