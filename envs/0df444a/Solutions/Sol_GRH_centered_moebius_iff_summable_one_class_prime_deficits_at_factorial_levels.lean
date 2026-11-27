-- Prove2me | solution 1 for GRH.centered_moebius_iff_summable_one_class_prime_deficits_at_factorial_levels
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:27:06.327216+00:00
-- url     : https://prove2.me/submissions/0e1b0a65-2306-445f-8b8f-135a9ab82355

import Theorems.Thm_GRH_unconditional_split_prime_deficit_in_the_siegel_walfisz_range
import Theorems.Thm_GRH_dirichlet_nonvanishing_of_integrable_one_class_prime_deficit
import Theorems.Thm_GRH_integrable_prime_deficit_from_summability_at_square_cutoffs
import Theorems.Thm_GRH_centered_moebius_implies_summable_square_prime_deficits
import Theorems.Thm_GRH_centered_moebius_at_modulus_iff_dirichlet_zero_free
import Theorems.Thm_GRH_centered_moebius_of_one_split_prime_class_at_factorial_squares
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Linarith

open GRH.OneSidedMoebius GRH.FactorialMoebius GRH.SplitPrimeLower GRH.PrimeDeficitMean

private theorem exponent_range (k : ℕ) : 1/2 < exponent k ∧ exponent k < 1 := by
  have lower : (0:ℝ) < 1/((k:ℝ)+3) := by positivity
  have upper : 1/((k:ℝ)+3) < (1/2:ℝ) := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+3)]
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  dsimp [exponent]
  constructor <;> linarith

private theorem choose_level (h : cofinalMean) (q : ℕ) [NeZero q] (x : ℝ) (hx : 1/2 < x) :
    ∃ k : ℕ, q ∣ level k ∧ exponent k < x ∧ squareMean (level k) (exponent k) := by
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

private theorem recover (h : cofinalMean) : centeredBound := by
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
  have lifted := GRH.dirichlet_nonvanishing_of_integrable_one_class_prime_deficit
    (level k) (exponent k) (by linarith) hi
    (GRH.integrable_prime_deficit_from_summability_at_square_cutoffs (level k) (exponent k) lo good) (DirichletCharacter.changeLevel divides χ)
    s hθ (fun e => notOne e.2)
  rw [DirichletCharacter.LFunction_changeLevel divides χ (Or.inr notOne)] at lifted
  exact (mul_ne_zero_iff.mp lifted).1

theorem solution : (centeredBound ↔ cofinalMean) ∧ (cofinalPrimeLower ↔ cofinalMean) ∧
    (¬centeredBound → ∃ B : ℕ, ∀ k : ℕ, B≤k →
      ¬ Summable (deficitTerm (level k) (exponent k)) ∧ Summable (deficitTerm (level k) 1)) := by
  have all (h : centeredBound) (k : ℕ) := GRH.centered_moebius_implies_summable_square_prime_deficits
    h (level k) (exponent k) (exponent_range k).1
  have iffMean : centeredBound ↔ cofinalMean :=
    ⟨fun h b => ⟨b,le_rfl,(all h b).2⟩,recover⟩
  refine ⟨iffMean,⟨fun h => iffMean.mp
    (GRH.centered_moebius_of_one_split_prime_class_at_factorial_squares.1 h),
    fun h b => ⟨b,le_rfl,(all (recover h) b).1⟩⟩,?_⟩
  intro h
  have hn := mt recover h
  unfold cofinalMean squareMean at hn
  push Not at hn
  obtain ⟨B,hB⟩ := hn
  exact ⟨B,fun k hk => ⟨hB k hk,GRH.unconditional_split_prime_deficit_in_the_siegel_walfisz_range.2 (level k)⟩⟩
