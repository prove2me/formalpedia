-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.prod_prod_X_sub_C_natCast_mul_add_eq_moore
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/edb45d58-f417-5f4c-9d2a-ead904ce9388

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore

set_option autoImplicit false

open IsLocalRing Polynomial

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "LocalChart.drinfeldForm x y"
namespace LocalChart
p2m_export "DrinfeldCurve.LocalChart" "drinfeldForm"
namespace MooreAux
p2m_open "DrinfeldCurve.LocalChart DrinfeldCurve"

variable (q : ℕ) [hq : Fact q.Prime]

theorem prod_sub_natCast (K : Type*) [CommRing K] [CharP K q] (t : K) :
    ∏ a : Fin q, (t - ((a : ℕ) : K)) = t ^ q - t := by
  classical
  have h1 : (1 : ℕ) < q := hq.out.one_lt
  have hmonic : (X ^ q - X : (ZMod q)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  have hroots : (X ^ q - X : (ZMod q)[X]).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod q)
    rwa [ZMod.card] at this
  have hcard : (X ^ q - X : (ZMod q)[X]).roots.card = (X ^ q - X : (ZMod q)[X]).natDegree := by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ h1]
    simp [ZMod.card]
  have hpoly := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [hroots] at hpoly
  have hpoly' : ∏ a : ZMod q, (X - C a) = (X ^ q - X : (ZMod q)[X]) := by
    rw [Finset.prod_eq_multiset_prod]; exact hpoly
  let φ : ZMod q →+* K := ZMod.castHom (dvd_refl q) K
  have h2 := congrArg (eval₂RingHom φ t) hpoly'
  simp only [map_prod, map_sub, map_pow, coe_eval₂RingHom, eval₂_X, eval₂_C] at h2
  rw [← h2]
  refine Fintype.prod_bijective (fun a : Fin q => ((a : ℕ) : ZMod q)) ?_ _ _ (fun a => ?_)
  · refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp [ZMod.card]⟩
    intro a b hab
    have := (ZMod.natCast_eq_natCast_iff' a b q).mp hab
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
    exact Fin.ext this
  · simp [φ, map_natCast]

theorem prod_sub_natCast_mul (D : Type*) [CommRing D] [IsDomain D] [CharP D q] (Y c : D) :
    ∏ a : Fin q, (Y - ((a : ℕ) : D) * c) = Y ^ q - c ^ (q - 1) * Y := by
  classical
  have h2 : 2 ≤ q := hq.out.two_le
  have hq1 : q - 1 + 1 = q := by omega
  by_cases hc : c = 0
  · subst hc
    simp only [mul_zero, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [zero_pow (by omega), zero_mul, sub_zero]
  · let L := FractionRing D
    have hinj : Function.Injective (algebraMap D L) := IsFractionRing.injective D L
    apply hinj
    simp only [map_prod, map_sub, map_mul, map_natCast, map_pow]
    set y := algebraMap D L Y with hy
    set d := algebraMap D L c with hd
    have hd0 : d ≠ 0 := by
      intro h
      apply hc
      apply hinj
      rw [map_zero]; exact h
    have huniv := prod_sub_natCast q L (y / d)
    have e1 : d * (y / d) = y := by rw [← mul_div_assoc, mul_div_cancel_left₀ y hd0]
    have hfac : ∏ a : Fin q, (y - ((a : ℕ) : L) * d) = d ^ q * ∏ a : Fin q, (y / d - ((a : ℕ) : L)) := by
      rw [show d ^ q = ∏ _a : Fin q, d by simp, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [mul_sub, e1]; ring
    rw [hfac, huniv]
    have e2 : d ^ q = d ^ (q - 1) * d := by rw [← pow_succ, hq1]
    calc d ^ q * ((y / d) ^ q - y / d) = (d * (y / d)) ^ q - d ^ (q - 1) * (d * (y / d)) := by
          rw [mul_sub, mul_pow, e2]; ring
      _ = y ^ q - d ^ (q - 1) * y := by rw [e1]

theorem natCast_pow_char (D : Type*) [CommRing D] [CharP D q] (n : ℕ) : ((n : D)) ^ q = (n : D) := by
  have := map_natCast (frobenius D q) n
  rwa [frobenius_def] at this

theorem sub_pow_sub_one_eq_geom_sum (D : Type*) [CommRing D] [IsDomain D] [CharP D q] (S T : D) (hST : S ≠ T) :
    (T - S) ^ (q - 1) = ∑ i ∈ Finset.range q, S ^ i * T ^ (q - 1 - i) := by
  have hq1 : q - 1 + 1 = q := by have := hq.out.two_le; omega
  have hne : S - T ≠ 0 := sub_ne_zero.mpr hST
  apply mul_right_cancel₀ hne
  rw [geom_sum₂_mul]
  have : (T - S) ^ (q - 1) * (S - T) = -((T - S) ^ q) := by
    rw [← hq1, pow_succ, hq1]; ring
  rw [this, sub_pow_char]; ring

theorem prod_sub_natCast_mul' (K : Type*) [CommRing K] [CharP K q] (Y c : K) :
    ∏ a : Fin q, (Y - ((a : ℕ) : K) * c) = Y ^ q - c ^ (q - 1) * Y := by
  classical
  have hU := prod_sub_natCast_mul q (MvPolynomial (Fin 2) (ZMod q)) (MvPolynomial.X 0) (MvPolynomial.X 1)
  let g : Fin 2 → K := fun i => if i = 0 then Y else c
  have h := congrArg (MvPolynomial.eval₂Hom (ZMod.castHom (dvd_refl q) K) g) hU
  simp only [map_prod, map_sub, map_mul, map_natCast, map_pow, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X] at h
  simpa [g] using h

theorem sub_pow_sub_one_eq_geom_sum' (K : Type*) [CommRing K] [CharP K q] (S T : K) :
    (T - S) ^ (q - 1) = ∑ i ∈ Finset.range q, S ^ i * T ^ (q - 1 - i) := by
  classical
  have hne : (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod q)) ≠ MvPolynomial.X 1 :=
    fun h => absurd (MvPolynomial.X_injective h) (by decide)
  have hU := sub_pow_sub_one_eq_geom_sum q (MvPolynomial (Fin 2) (ZMod q)) (MvPolynomial.X 0) (MvPolynomial.X 1) hne
  let g : Fin 2 → K := fun i => if i = 0 then S else T
  have h := congrArg (MvPolynomial.eval₂Hom (ZMod.castHom (dvd_refl q) K) g) hU
  simp only [map_sum, map_sub, map_mul, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at h
  simpa [g] using h

end DrinfeldCurve.LocalChart.MooreAux

open DrinfeldCurve.LocalChart.MooreAux in

theorem solution
    (q : ℕ) [Fact q.Prime] (R : Type) [CommRing R] [CharP R q] :
    ∏ a : Fin q, ∏ b : Fin q,
        (Polynomial.X - Polynomial.C
          (((a : ℕ) : MvPolynomial (Fin 2) R) * MvPolynomial.X 0 + ((b : ℕ) : MvPolynomial (Fin 2) R) * MvPolynomial.X 1) :
          Polynomial (MvPolynomial (Fin 2) R)) =
      Polynomial.X ^ (q ^ 2)
        - Polynomial.C (∑ i ∈ Finset.range (q + 1),
            (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i))) *
          Polynomial.X ^ q
        + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) R) * MvPolynomial.X 1 ^ q
            - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by have := (Fact.out : q.Prime).two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  set x : MvPolynomial (Fin 2) R := MvPolynomial.X 0 with hx
  set y : MvPolynomial (Fin 2) R := MvPolynomial.X 1 with hy

  have hH : (∑ i ∈ Finset.range (m + 1 + 1), x ^ (m * i) * y ^ (m * (m + 1 - i))) =
      x ^ (m * (m + 1)) + (y ^ (m + 1) - x ^ m * y) ^ m := by
    rw [Finset.sum_range_succ]
    have e0 : m * (m + 1 - (m + 1)) = 0 := by simp
    rw [e0, pow_zero, mul_one, add_comm]
    congr 1
    have hg : y ^ (m + 1) - x ^ m * y = y * (y ^ m - x ^ m) := by ring
    have hgeom := sub_pow_sub_one_eq_geom_sum' (m + 1) (MvPolynomial (Fin 2) R) (x ^ m) (y ^ m)
    simp only [Nat.add_sub_cancel] at hgeom
    rw [hg, mul_pow, hgeom, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
    have e1 : m + 1 - i = k + 1 := by omega
    have e2 : m - i = k := by omega
    rw [e1, e2, ← pow_mul, ← pow_mul]
    ring

  have hF : (x * y ^ (m + 1) - x ^ (m + 1) * y) ^ m = (y ^ (m + 1) - x ^ m * y) ^ m * x ^ m := by
    rw [← mul_pow]; congr 1; ring
  rw [hH, hF]

  rw [Finset.prod_comm]
  have inner : ∀ b : Fin (m + 1),
      ∏ a : Fin (m + 1), (X - C (((a : ℕ) : MvPolynomial (Fin 2) R) * x + ((b : ℕ) : MvPolynomial (Fin 2) R) * y)) =
        (X ^ (m + 1) - C x ^ m * X) - ((b : ℕ) : (MvPolynomial (Fin 2) R)[X]) * (C y ^ (m + 1) - C x ^ m * C y) := by
    intro b
    have hfac : ∀ a : Fin (m + 1), (X - C (((a : ℕ) : MvPolynomial (Fin 2) R) * x + ((b : ℕ) : MvPolynomial (Fin 2) R) * y)) =
        (X - ((b : ℕ) : (MvPolynomial (Fin 2) R)[X]) * C y) - ((a : ℕ) : (MvPolynomial (Fin 2) R)[X]) * C x := by
      intro a
      simp only [map_add, map_mul, map_natCast]
      ring
    rw [Finset.prod_congr rfl (fun a _ => hfac a),
      prod_sub_natCast_mul' (m + 1) _ (X - ((b : ℕ) : (MvPolynomial (Fin 2) R)[X]) * C y) (C x)]
    simp only [Nat.add_sub_cancel]
    rw [sub_pow_char (p := m + 1), mul_pow, natCast_pow_char (m + 1)]
    ring
  rw [Finset.prod_congr rfl (fun b _ => inner b),
    prod_sub_natCast_mul' (m + 1) _ (X ^ (m + 1) - C x ^ m * X) (C y ^ (m + 1) - C x ^ m * C y)]
  simp only [Nat.add_sub_cancel, map_add, map_pow, map_mul, map_sub]
  rw [sub_pow_char (p := m + 1) (X ^ (m + 1)) (C x ^ m * X)]
  ring

end S_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore (solution)
