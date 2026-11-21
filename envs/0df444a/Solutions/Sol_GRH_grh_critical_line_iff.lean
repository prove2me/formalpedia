-- Prove2me | solution 1 for GRH.grh_critical_line_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T22:32:22.797183+00:00
-- url     : https://prove2.me/submissions/e70451a6-2c4c-4160-8c7f-eb5ae936de08

import Mathlib

open DirichletCharacter Complex

namespace GRHCritIff

/-- The Archimedean factor does not vanish to the right of `0`. -/
lemma gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    gammaFactor χ s ≠ 0 := by
  unfold gammaFactor
  split_ifs
  · exact Gammaℝ_ne_zero_of_re_pos hs
  · exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- Right of `0`, `L(χ, s)` vanishes iff the completed `L`-function does. -/
lemma LFunction_eq_zero_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : LFunction χ s = 0 ↔ completedLFunction χ s = 0 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0), div_eq_zero_iff]
  have := gammaFactor_ne_zero χ hs
  tauto

/-- An Euler factor `1 - χ(p) p^{-s}` is nonzero for `Re s > 0`. -/
lemma euler_factor_ne_zero {M : ℕ} (χ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0 < s.re) : (1 : ℂ) - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : χ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hlt : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos]
    have hχ : ‖χ (p : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hpow : (p : ℝ) ^ (-s).re < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simp; linarith)
    calc ‖χ (p : ZMod M)‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re := by
          gcongr
      _ < 1 := by simpa using hpow
  rw [h1, norm_one] at hlt
  exact lt_irrefl _ hlt

end GRHCritIff

open GRHCritIff in
theorem solution :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) ↔
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      (1 / 2 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0) := by
  constructor
  · -- critical-line form for primitive characters ⇒ zero-free half-plane for all characters
    intro hc q _ χ s hs hpole
    rcases le_or_gt 1 s.re with h1 | h1
    · exact LFunction_ne_zero_of_one_le_re χ (not_and_or.mp hpole) h1
    · intro hL
      have hs1 : s ≠ 1 := fun h => by simp [h] at h1
      have hc0 : χ.conductor ≠ 0 := fun h =>
        (NeZero.ne q) (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))
      have : NeZero χ.conductor := ⟨hc0⟩
      have hfac := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
        (s := s) (Or.inr hs1)
      rw [changeLevel_primitiveCharacter] at hfac
      have hspos : 0 < s.re := by linarith
      have hprod : ∏ p ∈ q.primeFactors,
          ((1 : ℂ) - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun p hp =>
          euler_factor_ne_zero _ (Nat.prime_of_mem_primeFactors hp) hspos
      have hL' : LFunction χ.primitiveCharacter s = 0 := by
        rw [hL] at hfac
        rcases mul_eq_zero.mp hfac.symm with h | h
        · exact h
        · exact absurd h hprod
      have := hc χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s
        hspos h1 hL'
      linarith
  · -- zero-free half-plane ⇒ critical-line form, via the functional equation
    intro hz q _ χ hχ s hs0 hs1 hL
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- reflect the zero to `1 - s` for the primitive character `χ⁻¹`
      have hχi : χ⁻¹.IsPrimitive := by
        rw [isPrimitive_def, conductor_inv]; exact hχ
      have hcomp : completedLFunction χ s = 0 := (LFunction_eq_zero_iff χ hs0).mp hL
      have hfe := hχi.completedLFunction_one_sub s
      rw [inv_inv, hcomp, mul_zero] at hfe
      have hre : 0 < (1 - s).re := by simp; linarith
      have hL' : LFunction χ⁻¹ (1 - s) = 0 := (LFunction_eq_zero_iff χ⁻¹ hre).mpr hfe
      refine hz q χ⁻¹ (1 - s) (by simp; linarith) ?_ hL'
      rintro ⟨-, h⟩
      have : s = 0 := by linear_combination -h
      simp [this] at hs0
    · exact hz q χ s hgt (fun ⟨_, h⟩ => by simp [h] at hs1) hL
