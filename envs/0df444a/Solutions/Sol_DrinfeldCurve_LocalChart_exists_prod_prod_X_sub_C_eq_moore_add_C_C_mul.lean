-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d98d0cae-39cf-54f7-a5c5-9817c0709caa

import Mathlib
import Theorems.Thm_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul

set_option autoImplicit false

open IsLocalRing Polynomial

theorem solution
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (hq : (q : W) ∈ maximalIdeal W) :
    ∃ E : Polynomial (MvPolynomial (Fin 2) W),
      ∏ a : Fin q, ∏ b : Fin q,
          (Polynomial.X - Polynomial.C
            (((a : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 0 + ((b : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 1) :
            Polynomial (MvPolynomial (Fin 2) W)) =
        Polynomial.X ^ (q ^ 2)
          - Polynomial.C (∑ i ∈ Finset.range (q + 1),
              (MvPolynomial.X 0 : MvPolynomial (Fin 2) W) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i))) *
            Polynomial.X ^ q
          + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) W) * MvPolynomial.X 1 ^ q
              - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X
          + Polynomial.C (MvPolynomial.C π) * E := by
  classical
  have hprime : q.Prime := Fact.out
  set φ : W →+* ResidueField W := residue W with hφ
  have hφker : ∀ w : W, φ w = 0 ↔ w ∈ Ideal.span {π} := fun w => by rw [← hπ]; exact residue_eq_zero_iff w
  haveI : CharP (ResidueField W) q := (CharP.charP_iff_prime_eq_zero hprime).mpr (by
    rw [← map_natCast φ]; exact (hφker _).mpr (hπ ▸ hq))

  have hM := DrinfeldCurve.LocalChart.prod_prod_X_sub_C_natCast_mul_add_eq_moore q (ResidueField W)

  set f : MvPolynomial (Fin 2) W →+* MvPolynomial (Fin 2) (ResidueField W) := MvPolynomial.map φ with hf
  set Φ : Polynomial (MvPolynomial (Fin 2) W) →+* Polynomial (MvPolynomial (Fin 2) (ResidueField W)) := Polynomial.mapRingHom f with hΦ

  set L : Polynomial (MvPolynomial (Fin 2) W) := ∏ a : Fin q, ∏ b : Fin q,
      (Polynomial.X - Polynomial.C
        (((a : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 0 + ((b : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 1)) with hL
  set Rr : Polynomial (MvPolynomial (Fin 2) W) := Polynomial.X ^ (q ^ 2)
      - Polynomial.C (∑ i ∈ Finset.range (q + 1),
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) W) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i))) *
        Polynomial.X ^ q
      + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) W) * MvPolynomial.X 1 ^ q
          - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X with hRr
  have ΦX : Φ Polynomial.X = Polynomial.X := by simp [hΦ]
  have ΦC : ∀ a, Φ (Polynomial.C a) = Polynomial.C (f a) := by intro a; simp [hΦ]
  have fX : ∀ i, f (MvPolynomial.X i) = MvPolynomial.X i := by intro i; simp [hf]
  have hΦL : Φ L = ∏ a : Fin q, ∏ b : Fin q,
      (Polynomial.X - Polynomial.C
        (((a : ℕ) : MvPolynomial (Fin 2) (ResidueField W)) * MvPolynomial.X 0 + ((b : ℕ) : MvPolynomial (Fin 2) (ResidueField W)) * MvPolynomial.X 1)) := by
    simp only [hL, map_prod, map_sub, map_add, map_mul, map_natCast, ΦX, ΦC, fX]
  have hΦR : Φ Rr = Polynomial.X ^ (q ^ 2)
      - Polynomial.C (∑ i ∈ Finset.range (q + 1),
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ResidueField W)) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i))) *
        Polynomial.X ^ q
      + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) (ResidueField W)) * MvPolynomial.X 1 ^ q
          - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X := by
    simp only [hRr, map_add, map_sub, map_mul, map_pow, map_sum, map_natCast, ΦX, ΦC, fX]
  have hΦD : Φ (L - Rr) = 0 := by rw [map_sub, hΦL, hΦR, hM, sub_self]

  have hcoef : ∀ i : ℕ, (L - Rr).coeff i ∈ (Ideal.span {π} : Ideal W).map (MvPolynomial.C : W →+* MvPolynomial (Fin 2) W) := by
    intro i
    rw [MvPolynomial.mem_map_C_iff]
    intro m
    rw [← hφker]
    have h1 : (Φ (L - Rr)).coeff i = 0 := by rw [hΦD, Polynomial.coeff_zero]
    rw [hΦ, Polynomial.coe_mapRingHom, Polynomial.coeff_map] at h1
    have h2 := congrArg (MvPolynomial.coeff m) h1
    rw [hf, MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h2
    exact h2
  have hD : L - Rr ∈ (((Ideal.span {π} : Ideal W).map (MvPolynomial.C : W →+* MvPolynomial (Fin 2) W)).map
      (Polynomial.C : MvPolynomial (Fin 2) W →+* Polynomial (MvPolynomial (Fin 2) W))) :=
    Ideal.mem_map_C_iff.mpr hcoef
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton] at hD
  obtain ⟨E, hE⟩ := Ideal.mem_span_singleton'.mp hD
  refine ⟨E, ?_⟩
  show L = Rr + Polynomial.C (MvPolynomial.C π) * E
  rw [mul_comm, hE]; ring

end S_DrinfeldCurve_LocalChart_exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul (solution)
