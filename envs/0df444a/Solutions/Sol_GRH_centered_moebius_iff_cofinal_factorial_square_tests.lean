-- Prove2me | solution 1 for GRH.centered_moebius_iff_cofinal_factorial_square_tests
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:47:15.71711+00:00
-- url     : https://prove2.me/submissions/77ce0a64-b1ea-4ff4-a50a-9ed80d76f25c

import Definitions.Def_GRH_FactorialMoebius
import Theorems.Thm_GRH_centered_moebius_at_modulus_iff_dirichlet_zero_free
import Theorems.Thm_GRH_principal_moebius_upper_excludes_zeta_zeros_at_any_modulus
import Theorems.Thm_GRH_dirichlet_nonvanishing_of_one_sided_moebius_class_bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Linarith

open GRH.OneSidedMoebius GRH.FactorialMoebius

private theorem exponent_range (k : ℕ) : 1/2 < exponent k ∧ exponent k < 1 := by
  have lower : (0:ℝ) < 1/((k:ℝ)+3) := by positivity
  have upper : 1/((k:ℝ)+3) < (1/2:ℝ) := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+3)]
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  dsimp [exponent]
  constructor <;> linarith

private theorem choose_level (h : diagonal) (q : ℕ) [NeZero q] (x : ℝ) (hx : 1/2 < x) :
    ∃ k : ℕ, q ∣ level k ∧ exponent k < x ∧ upper (level k) (exponent k) := by
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

private theorem recover (h : diagonal) : centeredBound := by
  have ordinary : RiemannHypothesis := by
    apply (GRH.centered_moebius_at_modulus_iff_dirichlet_zero_free 1).2.2
    intro χ s hs pole
    by_cases high : 1 ≤ s.re
    · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp pole) high
    have notOne : s ≠ 1 := by intro e; simp [e] at high
    obtain ⟨k,_,hθ,good⟩ := choose_level h 1 s.re hs
    obtain ⟨lo,hi⟩ := exponent_range k
    have pr := GRH.principal_moebius_upper_excludes_zeta_zeros_at_any_modulus
      (level k) (exponent k) lo.le hi
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact pr.2 (pr.1 good) s hθ notOne
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
  have lifted := GRH.dirichlet_nonvanishing_of_one_sided_moebius_class_bounds
    ordinary (level k) (exponent k) lo hi good (DirichletCharacter.changeLevel divides χ)
    s hθ (fun e => notOne e.2)
  rw [DirichletCharacter.LFunction_changeLevel divides χ (Or.inr notOne)] at lifted
  exact (mul_ne_zero_iff.mp lifted).1

theorem solution : (centeredBound ↔ diagonal) ∧
    (¬centeredBound → ∃ B : ℕ, ∀ k : ℕ, B ≤ k →
      ∃ a : ZMod (level k), IsUnit a ∧ ∀ C : ℝ, 0 ≤ C → ∃ u : ℕ,
        C * ((u:ℝ)^2+1)^(exponent k) < residue a (u^2)) := by
  classical
  have criterion : centeredBound ↔ diagonal := by
    refine ⟨?_,recover⟩
    intro h B
    obtain ⟨hl,hr⟩ := exponent_range B
    exact ⟨B,le_rfl,(GRH.centered_moebius_at_modulus_iff_dirichlet_zero_free
      (level B)).1.mp (h (level B)) (exponent B) hl hr⟩
  refine ⟨criterion,?_⟩
  intro h
  have fails : ¬diagonal := fun d => h (criterion.mpr d)
  unfold diagonal upper at fails
  push Not at fails
  exact fails
