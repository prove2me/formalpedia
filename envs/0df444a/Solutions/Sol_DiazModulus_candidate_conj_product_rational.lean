-- Prove2me | solution 1 for DiazModulus.candidate_conj_product_rational
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:34:52.457661+00:00
-- url     : https://prove2.me/submissions/f181d390-885b-47d5-a063-74accfe7ed7e

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_gelfond_schneider

open Complex ComplexConjugate

namespace ConjProdRat

/-- Complex conjugation as a `ℚ`-algebra map, used to transport algebraicity. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

theorem alg_I : IsAlgebraic ℚ Complex.I := by
  refine IsAlgebraic.of_pow (n := 2) two_pos ?_
  rw [Complex.I_sq]
  exact (isAlgebraic_one (R := ℚ) (A := ℂ)).neg

end ConjProdRat

open ConjProdRat in
/-- `Re(pq)` algebraic forces `pq` algebraic (its imaginary part is then algebraic too, since
`|pq|` is), so `b = q / p̄ = pq / |p|²` is algebraic. Gelfond–Schneider at `b` and `l = p̄`
(`e^{p̄}` algebraic) forbids `b ∉ ℚ`, as `e^{b p̄} = e^q` is algebraic. -/
theorem solution (p q : ℂ) (hp : DiazModulus.IsCandidate p) (hq : DiazModulus.IsCandidate q)
    (hre : IsAlgebraic ℚ (((p * q).re : ℝ) : ℂ)) :
    ∃ r : ℚ, q = (r : ℂ) * conj p := by
  obtain ⟨hp0, hpn, hpe⟩ := hp
  obtain ⟨hq0, hqn, hqe⟩ := hq
  have hcp : conj p ≠ 0 := (map_ne_zero _).2 hp0
  -- `X² + Y² = |p|²|q|²`, so `Y` is algebraic
  have hsq : (p * q).re ^ 2 + (p * q).im ^ 2 = ‖p‖ ^ 2 * ‖q‖ ^ 2 := by
    rw [← mul_pow, ← Complex.norm_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hsqC : (((p * q).im : ℝ) : ℂ) ^ 2
      = ((‖p‖ : ℝ) : ℂ) ^ 2 * ((‖q‖ : ℝ) : ℂ) ^ 2 - (((p * q).re : ℝ) : ℂ) ^ 2 := by
    have h : ((((p * q).re ^ 2 + (p * q).im ^ 2 : ℝ)) : ℂ)
        = (((‖p‖ ^ 2 * ‖q‖ ^ 2 : ℝ)) : ℂ) := by
      rw [hsq]
    push_cast at h
    linear_combination h
  have hY : IsAlgebraic ℚ (((p * q).im : ℝ) : ℂ) := by
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [hsqC]
    exact ((hpn.pow 2).mul (hqn.pow 2)).sub (hre.pow 2)
  -- `pq = X + iY` is algebraic
  have hpq : IsAlgebraic ℚ (p * q) := by
    rw [← Complex.re_add_im (p * q)]
    exact hre.add (hY.mul alg_I)
  -- `p p̄ = |p|²` is algebraic
  have hρ : p * conj p = ((‖p‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hρalg : IsAlgebraic ℚ (p * conj p) := by rw [hρ]; exact hpn.pow 2
  -- `b = q / p̄ = pq / (p p̄)` is algebraic
  have hb : q / conj p = p * q / (p * conj p) := (mul_div_mul_left q (conj p) hp0).symm
  have hbalg : IsAlgebraic ℚ (q / conj p) := by
    rw [hb, div_eq_mul_inv]
    exact hpq.mul hρalg.inv
  by_contra hne
  have hbq : ∀ r : ℚ, q / conj p ≠ (r : ℂ) := by
    intro r hr
    apply hne
    refine ⟨r, ?_⟩
    rw [← hr, div_mul_cancel₀ q hcp]
  have hgs := Schanuel.gelfond_schneider (q / conj p) (conj p) hbalg hbq
    (by rw [Complex.exp_conj]; exact alg_conj hpe) hcp
  rw [div_mul_cancel₀ q hcp] at hgs
  exact hgs hqe

#print axioms solution
