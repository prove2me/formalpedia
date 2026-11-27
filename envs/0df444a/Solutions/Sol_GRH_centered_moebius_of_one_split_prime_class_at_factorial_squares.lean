-- Prove2me | solution 1 for GRH.centered_moebius_of_one_split_prime_class_at_factorial_squares
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:48:25.422665+00:00
-- url     : https://prove2.me/submissions/006cdf5c-167a-4183-9044-658d5b11c737

import Theorems.Thm_GRH_dirichlet_zero_free_of_prime_lower_bound_in_identity_class
import Theorems.Thm_GRH_centered_moebius_at_modulus_iff_dirichlet_zero_free
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Linarith

open GRH.OneSidedMoebius GRH.FactorialMoebius GRH.SplitPrimeLower

private theorem exponent_range (k : ℕ) : 1/2 < exponent k ∧ exponent k < 1 := by
  have lower : (0:ℝ) < 1/((k:ℝ)+3) := by positivity
  have upper : 1/((k:ℝ)+3) < (1/2:ℝ) := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+3)]
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  dsimp [exponent]
  constructor <;> linarith

private theorem choose_level (h : cofinalPrimeLower) (q : ℕ) [NeZero q] (x : ℝ) (hx : 1/2 < x) :
    ∃ k : ℕ, q ∣ level k ∧ exponent k < x ∧ squareLower (level k) (exponent k) := by
  obtain ⟨B,hB⟩ := exists_nat_gt (1/(x-1/2))
  obtain ⟨k,hk,good⟩ := h (max q B)
  have hq : q ≤ k := (le_max_left ..).trans hk
  have hn : B ≤ k := (le_max_right ..).trans hk
  have hn' : (B:ℝ) ≤ (k:ℝ) := by exact_mod_cast hn
  have h1 : 1/(x-1/2) < (k:ℝ)+3 := by linarith
  have h2 := (div_lt_iff₀ (sub_pos.mpr hx)).mp h1
  have h3 : 1/((k:ℝ)+3) < x-1/2 := (div_lt_iff₀ (by positivity)).mpr (by simpa [mul_comm] using h2)
  refine ⟨k,Nat.dvd_factorial (NeZero.pos q) (by omega),?_,good⟩
  dsimp [exponent]; linarith

private theorem recover (h : cofinalPrimeLower) : centeredBound := by
  intro q inst
  have target := GRH.centered_moebius_at_modulus_iff_dirichlet_zero_free q
  apply target.1.mpr
  apply target.2.1.mpr
  intro χ s hs pole
  by_cases high : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp pole) high
  have notOne : s ≠ 1 := by intro e; simp [e] at high
  obtain ⟨k,divides,hθ,good⟩ := choose_level h q s.re hs
  obtain ⟨lo,hi⟩ := exponent_range k
  have lifted := GRH.dirichlet_zero_free_of_prime_lower_bound_in_identity_class
    (level k) (exponent k) lo.le hi good (DirichletCharacter.changeLevel divides χ)
    s hθ (fun e => notOne e.2)
  rw [DirichletCharacter.LFunction_changeLevel divides χ (Or.inr notOne)] at lifted
  exact (mul_ne_zero_iff.mp lifted).1

theorem solution : (cofinalPrimeLower → centeredBound) ∧
    (¬centeredBound → ∃ B : ℕ, ∀ k : ℕ, B ≤ k → ∀ C : ℝ, 0 ≤ C → ∃ u : ℕ,
      ((level k).totient:ℝ)*primeWeight (level k) (u^2) <
        (u:ℝ)^2-C*((u:ℝ)^2+1)^(exponent k)) := by
  classical
  refine ⟨recover,?_⟩
  intro hn
  have h := mt recover hn
  unfold cofinalPrimeLower squareLower at h
  push Not at h
  exact h
