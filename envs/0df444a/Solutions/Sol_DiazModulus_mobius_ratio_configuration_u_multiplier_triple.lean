-- Prove2me | solution 1 for DiazModulus.mobius_ratio_configuration_u_multiplier_triple
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:27:19.873705+00:00
-- url     : https://prove2.me/submissions/07d4f821-c2ac-4bd2-9eb6-6e57f80a8398

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A degree-one ratio turns a configuration into three free `t` with `t, u t ∈ W`

Write `p = aX + b`, `q = cX + d` (`max(deg p, deg q) = 1`). First `q ≠ 0`: otherwise `x₀ p(u) = 0`,
so `p = 0` (`u` is transcendental over `Q̄`) and `0, 0` are not coprime; hence `q(u) ≠ 0`.
Next `D = ad - bc ≠ 0`. If `c ≠ 0`, then `D = 0` gives `c p(u) = a q(u)`, so `c x₁ = a x₀` and the
freeness of `x` forces `c = 0`. If `c = 0`, then `q(u) = d ≠ 0`, so `D = 0` forces `a = 0`, and both
`p` and `q` have zero coefficient of `X`, against `max(deg p, deg q) = 1`.
Put `y'ⱼ = x₀ yⱼ / q(u)`, a non-zero multiple of the free family `y`, so `y'` is free. As
`x₀ yⱼ = q(u) y'ⱼ` and `x₁ yⱼ = p(u) y'ⱼ` (from `x₁ q(u) = x₀ p(u)`), inverting the matrix of
`span(q, p) = span(1, X)` gives `D y'ⱼ = a x₀ yⱼ - c x₁ yⱼ` and `D u y'ⱼ = d x₁ yⱼ - b x₀ yⱼ`; both
lie in `W`, and so do `y'ⱼ` and `u y'ⱼ` after dividing by `D ∈ Q̄`.
-/

namespace R20_C16

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem aeval_injective {u : ℂ} (hu : u ∉ Qbar) :
    Function.Injective (aeval (R := ↥Qbar) u) :=
  (injective_iff_map_eq_zero _).2 fun P hP => transcendental_iff.1 (tr_of_not_mem hu) P hP

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_eq (a : ↥Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

theorem aeval_lin (u : ℂ) {f : (↥Qbar)[X]} (h : f.natDegree ≤ 1) :
    aeval u f = (f.coeff 1 : ℂ) * u + (f.coeff 0 : ℂ) := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one h]
  simp only [map_add, map_mul, aeval_C, aeval_X, am]

theorem coeff_one_ne_zero {f : (↥Qbar)[X]} (h : f.natDegree = 1) : f.coeff 1 ≠ 0 := by
  have := leadingCoeff_ne_zero.2 (ne_zero_of_natDegree_gt (show 0 < f.natDegree by omega))
  rwa [leadingCoeff, h] at this

/-- From `c x₁ = a x₀` with `x` free, `c = 0`. -/
theorem free_rel {x : Fin 2 → ℂ} (hx : LinearIndependent (↥Qbar) x) (a c : ↥Qbar)
    (h : (c : ℂ) * x 1 = a * x 0) : c = 0 := by
  have hxv : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hxv] at hx
  have := (LinearIndependent.pair_iff.1 hx a (-c) (by
    rw [neg_smul, smul_eq, smul_eq]; linear_combination -h)).2
  exact neg_eq_zero.1 this

end R20_C16

open DiazModulus R20_C16 Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 1)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    ∃ y' : Fin 3 → ℂ, LinearIndependent (↥Qbar) y' ∧ ∀ j, y' j ∈ W ∧ u * y' j ∈ W := by
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at hpq
    have hp0 : p = 0 := aeval_injective hu (by
      rw [map_zero]; exact (mul_eq_zero.1 hpq.symm).resolve_left hx0)
    rw [hp0] at hcop
    exact not_isCoprime_zero_zero hcop
  have hqu : aeval u q ≠ 0 := fun h0 => hq0 (aeval_injective hu (by rw [h0, map_zero]))
  have hp1 := aeval_lin u (f := p) (by omega)
  have hq1 := aeval_lin u (f := q) (by omega)
  set a := p.coeff 1 with ha
  set b := p.coeff 0 with hb
  set c := q.coeff 1 with hc
  set d := q.coeff 0 with hd
  rw [hp1, hq1] at hpq
  rw [hq1] at hqu
  -- the determinant `ad - bc` is not zero
  set D : ↥Qbar := a * d - b * c with hDdef
  have hDc : (D : ℂ) = (a : ℂ) * d - b * c := by rw [hDdef]; push_cast; ring
  have hD : D ≠ 0 := by
    intro hD0
    have hD' : (a : ℂ) * d - b * c = 0 := by rw [← hDc, hD0]; rfl
    by_cases hc0 : (c : ℂ) = 0
    · have hd0 : (d : ℂ) ≠ 0 := by rw [hc0, zero_mul, zero_add] at hqu; exact hqu
      have ha0 : (a : ℂ) = 0 := (mul_eq_zero.1 (by rw [hc0] at hD'; linear_combination hD')).resolve_right hd0
      have ha0' : a = 0 := by exact_mod_cast ha0
      have hc0' : c = 0 := by exact_mod_cast hc0
      rcases (show p.natDegree = 1 ∨ q.natDegree = 1 by omega) with h | h
      · exact coeff_one_ne_zero h ha0'
      · exact coeff_one_ne_zero h hc0'
    · apply hc0
      have key : (c : ℂ) * x 1 = a * x 0 := by
        apply mul_right_cancel₀ hqu
        linear_combination (c : ℂ) * hpq - x 0 * hD'
      rw [free_rel hx a c key]; rfl
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  set Qi := ((c : ℂ) * u + d)⁻¹ with hQidef
  have hQi : ((c : ℂ) * u + d) * Qi = 1 := mul_inv_cancel₀ hqu
  have hQi0 : Qi ≠ 0 := inv_ne_zero hqu
  refine ⟨fun j => x 0 * Qi * y j, ?_, fun j => ⟨?_, ?_⟩⟩
  · exact hy.map' (LinearMap.mulLeft (↥Qbar) (x 0 * Qi))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (mul_ne_zero hx0 hQi0)))
  · have e1 : (D : ℂ) * (x 0 * Qi * y j) = a * (x 0 * y j) - c * (x 1 * y j) := by
      rw [hDc]
      linear_combination (a * (x 0 * y j) - c * (x 1 * y j)) * hQi + (c * y j * Qi) * hpq
    have e : x 0 * Qi * y j = D⁻¹ • (a • (x 0 * y j) - c • (x 1 * y j)) := by
      rw [smul_eq, smul_eq, smul_eq, ← e1]
      push_cast
      rw [inv_mul_cancel_left₀ hDne]
    show x 0 * Qi * y j ∈ W
    rw [e]
    exact W.smul_mem _ (W.sub_mem (W.smul_mem _ (hxy 0 j)) (W.smul_mem _ (hxy 1 j)))
  · have e1 : (D : ℂ) * (u * (x 0 * Qi * y j)) = d * (x 1 * y j) - b * (x 0 * y j) := by
      rw [hDc]
      linear_combination (d * (x 1 * y j) - b * (x 0 * y j)) * hQi - (d * y j * Qi) * hpq
    have e : u * (x 0 * Qi * y j) = D⁻¹ • (d • (x 1 * y j) - b • (x 0 * y j)) := by
      rw [smul_eq, smul_eq, smul_eq, ← e1]
      push_cast
      rw [inv_mul_cancel_left₀ hDne]
    show u * (x 0 * Qi * y j) ∈ W
    rw [e]
    exact W.smul_mem _ (W.sub_mem (W.smul_mem _ (hxy 1 j)) (W.smul_mem _ (hxy 0 j)))
