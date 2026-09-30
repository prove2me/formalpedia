-- Prove2me | solution 1 for FourExp.exists_iteratedDeriv_reduced_presentation_column
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:22:20.126983+00:00
-- url     : https://prove2.me/submissions/6bdd418a-efe8-4527-b454-59b51baf33c8

import Mathlib
import Theorems.Thm_FourExp_exists_iteratedDeriv_presentation_column
import Theorems.Thm_Transcendence_exists_modByMonic_length_le
import Theorems.Thm_Transcendence_length_mul_le

/-!
# The derivatives with integer unknowns, reduced modulo `Q`, in the column case

As in `FourExp.exists_iteratedDeriv_reduced_presentation`, with
`FourExp.exists_iteratedDeriv_presentation_column` in place of
`FourExp.exists_iteratedDeriv_presentation`. Write `φ(P) = P(ω, ω₁)` and take
`R_{ijkμν} = (X^μ Y^ν P_{ijk}) mod Q`, where `P_{ijk}` and `Λ` present the derivatives with
coefficients `f_{ijk} = ∑ q_{ijkμν} ω^μ ω₁^ν`. Since `φ(Q) = 0`,
`φ(R_{ijkμν}) = ω^μ ω₁^ν φ(P_{ijk})`, which gives the identity after summing against `q_{ijkμν}`.

The only change is in the degrees. With `Z = 1 + m + S` and `Z' = 1 + m + S + T a`, the
`P_{ijk}` have length at most `c₄^(c₄ X') Y'^(c₄ Z)` and degrees at most `c₄ Z'` in `X` and in `Y`.
So `X^μ Y^ν P_{ijk}` has `Y`-degree at most `ν + c₄ Z'` with `ν < deg Q`, and the reduction
modulo `Q` multiplies the length by at most `C₀^(deg Q + c₄ Z')` and adds at most
`C₀ (ν + c₄ Z')` to the `X`-degrees. Both are absorbed into one constant `c`, using
`Z ≤ Z' ≤ X' = 1 + m + S + T (a + b)`: the length factor `Y'^(c Z)` keeps its exponent, and the
`X`-degrees are at most `M + c Z'`.
-/

namespace T2_exists_iteratedDeriv_reduced_presentation_column

open Polynomial

/-- The monomial `X^μ Y^ν` has length one. -/
lemma length_monomial (μ ν : ℕ) :
    ∑ k ∈ (C (X ^ μ) * X ^ ν : ℤ[X][X]).support,
      ∑ i ∈ ((C (X ^ μ) * X ^ ν : ℤ[X][X]).coeff k).support,
        (((C (X ^ μ) * X ^ ν : ℤ[X][X]).coeff k).coeff i).natAbs = 1 := by
  rw [C_mul_X_pow_eq_monomial, support_monomial _ (pow_ne_zero _ X_ne_zero), Finset.sum_singleton,
    coeff_monomial_same, support_X_pow, Finset.sum_singleton, coeff_X_pow_self]
  rfl

/-- Multiplying by `X^μ Y^ν` raises the `X`-degrees of the coefficients by at most `μ` and the
`Y`-degree by at most `ν`. -/
lemma monomial_mul_degrees (P : ℤ[X][X]) (μ ν : ℕ) {e n : ℕ}
    (he : ∀ k, (P.coeff k).natDegree ≤ e) (hn : P.natDegree ≤ n) :
    (∀ k, ((C (X ^ μ) * X ^ ν * P).coeff k).natDegree ≤ μ + e) ∧
      (C (X ^ μ) * X ^ ν * P).natDegree ≤ ν + n := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    refine natDegree_mul_le.trans ?_
    split_ifs
    · exact add_le_add (natDegree_X_pow_le μ) (he _)
    · rw [natDegree_zero, add_zero]
      exact (natDegree_X_pow_le μ).trans (Nat.le_add_right μ e)
  · calc (C (X ^ μ) * X ^ ν * P).natDegree
        ≤ (C (X ^ μ) * X ^ ν : ℤ[X][X]).natDegree + P.natDegree := natDegree_mul_le
      _ ≤ ((C (X ^ μ) : ℤ[X][X]).natDegree + (X ^ ν : ℤ[X][X]).natDegree) + P.natDegree :=
          Nat.add_le_add_right natDegree_mul_le _
      _ ≤ (0 + ν) + n := by
          gcongr
          · exact (natDegree_C _).le
          · exact natDegree_X_pow_le ν
      _ = ν + n := by ring

end T2_exists_iteratedDeriv_reduced_presentation_column

open Polynomial T2_exists_iteratedDeriv_reduced_presentation_column in
theorem solution
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp₂ : ∀ i : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * y₂)))
    (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ))
    (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0)
    (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) *
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) :
    ∃ c : ℕ, ∀ S T M a b m : ℕ, ∃ Λ : ℂ, Λ ≠ 0 ∧
      ‖Λ‖ ≤ (c : ℝ) ^ (c * (1 + m + S + T * (a + b))) ∧
      ∃ R : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → Polynomial (Polynomial ℤ),
        (∀ i j k μ ν, (R i j k μ ν).natDegree < Q.natDegree) ∧
        (∀ i j k μ ν, ∑ r ∈ (R i j k μ ν).support, ∑ h ∈ ((R i j k μ ν).coeff r).support,
            (((R i j k μ ν).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S))) ∧
        (∀ i j k μ ν r, ((R i j k μ ν).coeff r).natDegree ≤ M + c * (1 + m + S + T * a)) ∧
        ∀ q : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → ℤ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              (∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
                ((q i j k μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) * z ^ (i : ℕ) *
                Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁
            (∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T, ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
              Polynomial.C (Polynomial.C (q i j k μ ν)) * R i j k μ ν) := by
  obtain ⟨c₄, h4⟩ := FourExp.exists_iteratedDeriv_presentation_column x₁ x₂ y₁ y₂ hexp₂ ω ω₁
    D E G H hD hE hG hH
  obtain ⟨C₀, h3⟩ := Transcendence.exists_modByMonic_length_le Q
  -- `Q ≠ 1`, since `φ(Q) = 0`
  have hQ1 : Q ≠ 1 := by
    rintro rfl
    rw [eval₂_one] at hQroot
    exact one_ne_zero hQroot
  refine ⟨C₀ + Q.natDegree + 2 * c₄ + C₀ * Q.natDegree + C₀ * c₄ + 1,
    fun S T M a b m => ?_⟩
  set c := C₀ + Q.natDegree + 2 * c₄ + C₀ * Q.natDegree + C₀ * c₄ + 1 with hc
  obtain ⟨Λ, hΛ, hΛn, P, hPl, hPx, hPy, hPid⟩ := h4 S T a b m
  have hTa : T * a ≤ T * (a + b) := Nat.mul_le_mul_left T (Nat.le_add_right a b)
  set X' := 1 + m + S + T * (a + b) with hX'
  set Y' := 1 + m + S + T + a + b with hY'
  set Z' := 1 + m + S + T * a with hZ'
  set Z := 1 + m + S with hZ
  have hZ'1 : 1 ≤ Z' := by omega
  have hZX : Z' ≤ X' := by omega
  have hZY : 1 ≤ Y' := by omega
  have hc1 : 1 ≤ c := by omega
  refine ⟨Λ, hΛ, ?_, fun i j k μ ν => (C (X ^ (μ : ℕ)) * X ^ (ν : ℕ) * P i j k) %ₘ Q,
    fun i j k μ ν => natDegree_modByMonic_lt _ hQm hQ1, fun i j k μ ν => ?_,
    fun i j k μ ν r => ?_, fun q => ?_⟩
  · -- the factor `Λ`: `c₄^(c₄ X') ≤ c^(c X')`
    refine hΛn.trans ?_
    calc (c₄ : ℝ) ^ (c₄ * X') ≤ (c : ℝ) ^ (c₄ * X') :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : c₄ ≤ c)) _
      _ ≤ (c : ℝ) ^ (c * X') :=
          pow_le_pow_right₀ (by exact_mod_cast hc1) (Nat.mul_le_mul_right _ (by omega))
  · -- the length: `C₀^(deg Q + c₄ Z') c₄^(c₄ X') Y'^(c₄ Z) ≤ c^(c X') Y'^(c Z)`
    obtain ⟨hsx, hsy⟩ := monomial_mul_degrees (P i j k) μ ν (hPx i j k) (hPy i j k)
    have hν : (ν : ℕ) + c₄ * Z' ≤ Q.natDegree + c₄ * Z' := by have := ν.2; omega
    have hmul := Transcendence.length_mul_le
      (C (X ^ (μ : ℕ)) * X ^ (ν : ℕ)) (P i j k)
    rw [length_monomial, one_mul] at hmul
    refine ((h3 _ _ _ _ (hmul.trans (hPl i j k)) hsx (hsy.trans hν)).1).trans ?_
    have hexp1 : Q.natDegree + c₄ * Z' + c₄ * X' ≤ c * X' := by
      have h1 : Q.natDegree ≤ Q.natDegree * X' := Nat.le_mul_of_pos_right _ (by omega)
      have h2 : c₄ * Z' ≤ c₄ * X' := Nat.mul_le_mul_left _ hZX
      have h3 := Nat.mul_le_mul_right X' (show Q.natDegree + c₄ + c₄ ≤ c by omega)
      rw [Nat.add_mul, Nat.add_mul] at h3
      omega
    calc C₀ ^ (Q.natDegree + c₄ * Z') * (c₄ ^ (c₄ * X') * Y' ^ (c₄ * Z))
        ≤ c ^ (Q.natDegree + c₄ * Z') * (c ^ (c₄ * X') * Y' ^ (c₄ * Z)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
            (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _))
      _ = c ^ (Q.natDegree + c₄ * Z' + c₄ * X') * Y' ^ (c₄ * Z) := by ring
      _ ≤ c ^ (c * X') * Y' ^ (c * Z) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right hc1 hexp1)
            (Nat.pow_le_pow_right hZY (Nat.mul_le_mul_right _ (by omega)))
  · -- the `X`-degree: `μ + c₄ Z' + C₀ (ν + c₄ Z') ≤ M + c Z'`
    obtain ⟨hsx, hsy⟩ := monomial_mul_degrees (P i j k) μ ν (hPx i j k) (hPy i j k)
    have hmul := Transcendence.length_mul_le
      (C (X ^ (μ : ℕ)) * X ^ (ν : ℕ)) (P i j k)
    rw [length_monomial, one_mul] at hmul
    refine ((h3 _ _ _ _ (hmul.trans (hPl i j k)) hsx hsy).2 r).trans ?_
    have hμ : (μ : ℕ) ≤ M := μ.2.le
    have hν : (ν : ℕ) ≤ Q.natDegree := ν.2.le
    have h1 : C₀ * ((ν : ℕ) + c₄ * Z') ≤ C₀ * Q.natDegree * Z' + C₀ * c₄ * Z' := by
      have e1 : C₀ * (ν : ℕ) ≤ C₀ * Q.natDegree * Z' :=
        (Nat.mul_le_mul_left C₀ hν).trans (Nat.le_mul_of_pos_right _ hZ'1)
      have e2 : C₀ * ((ν : ℕ) + c₄ * Z') = C₀ * ν + C₀ * c₄ * Z' := by ring
      omega
    have h2 := Nat.mul_le_mul_right Z' (show c₄ + C₀ * Q.natDegree + C₀ * c₄ ≤ c by omega)
    rw [Nat.add_mul, Nat.add_mul] at h2
    omega
  · -- the identity: `φ((X^μ Y^ν P) mod Q) = ω^μ ω₁^ν φ(P)` because `φ(Q) = 0`
    have key := hPid (fun i j k => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
      ((q i j k μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ))
    refine key.trans ?_
    have hφ : ∀ (P : ℤ[X][X]) (μ ν : ℕ),
        eval₂ (eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ ((C (X ^ μ) * X ^ ν * P) %ₘ Q) =
          ω ^ μ * ω₁ ^ ν * eval₂ (eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ P := by
      intro P μ ν
      have h := congrArg (eval₂ (eval₂RingHom (Int.castRingHom ℂ) ω) ω₁)
        (modByMonic_add_div (C (X ^ μ) * X ^ ν * P) Q)
      rw [eval₂_add, eval₂_mul, hQroot, zero_mul, add_zero] at h
      rw [h]
      simp only [eval₂_mul, eval₂_C, eval₂_X_pow, coe_eval₂RingHom]
    simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, hφ, coe_eval₂RingHom, Int.coe_castRingHom,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun μ _ =>
        Finset.sum_congr rfl fun ν _ => ?_
    ring
