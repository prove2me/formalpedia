-- Prove2me | solution 1 for CelestialWedge.poisson_realization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T00:54:17.14399+00:00
-- url     : https://prove2.me/submissions/01ab16b1-b131-46f2-a7d1-41126535ec30

import Mathlib
import Definitions.Def_celestial_wedge_algebra

set_option autoImplicit false

namespace CW34631ce9

open MvPolynomial CelestialWedge

lemma pow_pred_mul (a c : ℕ) (x : MvPolynomial (Fin 2) ℂ) :
    (a : MvPolynomial (Fin 2) ℂ) * (x ^ (a - 1) * x ^ c) =
      (a : MvPolynomial (Fin 2) ℂ) * x ^ (a + c - 1) := by
  rcases a with _ | a
  · simp
  · rw [← pow_add]
    congr 2
    omega

lemma poisson_mono (a b c d : ℕ) :
    poisson (X 0 ^ a * X 1 ^ b) (X 0 ^ c * X 1 ^ d) =
      C ((a : ℂ) * d - b * c) * (X 0 ^ (a + c - 1) * X 1 ^ (b + d - 1)) := by
  have h01 : pderiv (0 : Fin 2) (X 1 : MvPolynomial (Fin 2) ℂ) = 0 :=
    pderiv_X_of_ne (by decide)
  have h10 : pderiv (1 : Fin 2) (X 0 : MvPolynomial (Fin 2) ℂ) = 0 :=
    pderiv_X_of_ne (by decide)
  simp only [poisson, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self, h01, h10,
    nsmul_eq_mul, smul_eq_mul, mul_one]
  have e1 := pow_pred_mul a c (X 0)
  have e2 := pow_pred_mul d b (X 1)
  have e3 := pow_pred_mul b d (X 1)
  have e4 := pow_pred_mul c a (X 0)
  rw [show d + b - 1 = b + d - 1 by omega] at e2
  rw [show c + a - 1 = a + c - 1 by omega] at e4
  simp only [map_sub, map_mul, map_natCast]
  linear_combination ((X 1 ^ b * (d : MvPolynomial (Fin 2) ℂ) * X 1 ^ (d - 1)) * e1
    + (a : MvPolynomial (Fin 2) ℂ) * X 0 ^ (a + c - 1) * e2
    - ((X 0 ^ a * (c : MvPolynomial (Fin 2) ℂ) * X 0 ^ (c - 1))) * e3
    - (b : MvPolynomial (Fin 2) ℂ) * X 1 ^ (b + d - 1) * e4)

lemma poisson_add_left (f g h : MvPolynomial (Fin 2) ℂ) :
    poisson (f + g) h = poisson f h + poisson g h := by
  simp only [poisson, map_add]; ring

lemma poisson_add_right (f g h : MvPolynomial (Fin 2) ℂ) :
    poisson f (g + h) = poisson f g + poisson f h := by
  simp only [poisson, map_add]; ring

lemma poisson_smul_left (c : ℂ) (f g : MvPolynomial (Fin 2) ℂ) :
    poisson (c • f) g = c • poisson f g := by
  rw [smul_eq_C_mul, smul_eq_C_mul]
  simp only [poisson, Derivation.leibniz, pderiv_C, smul_eq_mul]
  ring

lemma poisson_smul_right (c : ℂ) (f g : MvPolynomial (Fin 2) ℂ) :
    poisson f (c • g) = c • poisson f g := by
  rw [smul_eq_C_mul, smul_eq_C_mul]
  simp only [poisson, Derivation.leibniz, pderiv_C, smul_eq_mul]
  ring

lemma toPoly_single (x : WedgeIndex) (c : ℂ) :
    toPoly (Finsupp.single x c) = c • monomialOf x.1.1 x.1.2 := by
  simp [toPoly, Finsupp.linearCombination_single]

lemma bracket_single (x y : WedgeIndex) (c d : ℂ) :
    bracket (Finsupp.single x c) (Finsupp.single y d) = (c * d) • bracketGen x y := by
  simp [bracket, Finsupp.linearCombination_single, smul_smul]

lemma mono_eq (p m : ℚ) (a b : ℕ) (ha : p + m - 1 = a) (hb : p - m - 1 = b) :
    monomialOf p m = X 0 ^ a * X 1 ^ b := by
  simp [monomialOf, ha, hb]

lemma key (x y : WedgeIndex) :
    toPoly (bracketGen x y) =
      (1 / 2 : ℂ) • poisson (monomialOf x.1.1 x.1.2) (monomialOf y.1.1 y.1.2) := by
  obtain ⟨a, b, ha, hb⟩ := x.2
  obtain ⟨c, d, hc, hd⟩ := y.2
  rw [mono_eq _ _ a b ha hb, mono_eq _ _ c d hc hd, poisson_mono]
  unfold bracketGen
  split_ifs with h
  · have h' := h
    obtain ⟨e, f, he, hf⟩ := h'
    have hz : toPoly (Finsupp.single
        (⟨(x.1.1 + y.1.1 - 2, x.1.2 + y.1.2), h⟩ : WedgeIndex) (1 : ℂ)) =
        X 0 ^ e * X 1 ^ f := by
      exact (toPoly_single _ 1).trans ((one_smul ℂ _).trans (mono_eq _ _ e f he hf))
    rw [map_smul]
    refine (congrArg (fun P => ((structConst x.1.1 x.1.2 y.1.1 y.1.2 : ℚ) : ℂ) • P) hz).trans ?_
    have hac : a + c = e + 1 := by
      have : ((a + c : ℕ) : ℚ) = ((e + 1 : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have hbd : b + d = f + 1 := by
      have : ((b + d : ℕ) : ℚ) = ((f + 1 : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have hq : structConst x.1.1 x.1.2 y.1.1 y.1.2 = ((a : ℚ) * d - b * c) / 2 := by
      rw [← ha, ← hb, ← hc, ← hd]; unfold structConst; ring
    have hs : ((structConst x.1.1 x.1.2 y.1.1 y.1.2 : ℚ) : ℂ) = ((a : ℂ) * d - b * c) / 2 := by
      rw [hq]; push_cast; ring
    rw [show a + c - 1 = e by omega, show b + d - 1 = f by omega, hs, ← smul_eq_C_mul,
      smul_smul]
    congr 1
    ring
  · have hk : (a : ℂ) * d - b * c = 0 := by
      by_cases h1 : 1 ≤ a + c
      · by_cases h2 : 1 ≤ b + d
        · exfalso
          apply h
          refine ⟨a + c - 1, b + d - 1, ?_, ?_⟩
          · push_cast [Nat.cast_sub h1]; linarith
          · push_cast [Nat.cast_sub h2]; linarith
        · obtain ⟨rfl, rfl⟩ : b = 0 ∧ d = 0 := by omega
          simp
      · obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by omega
        simp
    rw [hk, map_zero]
    simp

end CW34631ce9

open CelestialWedge in
theorem solution (X Y : WedgeSpace) :
    toPoly (bracket X Y) = (1 / 2 : ℂ) • poisson (toPoly X) (toPoly Y) := by
  induction X using Finsupp.induction_linear with
  | zero => simp [poisson]
  | add f g hf hg =>
    rw [map_add, LinearMap.add_apply, map_add, hf, hg, map_add, CW34631ce9.poisson_add_left, smul_add]
  | single x c =>
    induction Y using Finsupp.induction_linear with
    | zero => simp [poisson]
    | add f g hf hg =>
      rw [map_add, map_add, hf, hg, map_add, CW34631ce9.poisson_add_right, smul_add]
    | single y d =>
      rw [CW34631ce9.bracket_single, map_smul, CW34631ce9.key, CW34631ce9.toPoly_single, CW34631ce9.toPoly_single, CW34631ce9.poisson_smul_left,
        CW34631ce9.poisson_smul_right, smul_smul, smul_smul, smul_smul]
      congr 1
      ring
