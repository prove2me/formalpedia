-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.one_le_zetaMul_prime_pow_even
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:34.018638+00:00
-- url     : https://prove2.me/submissions/fa669e17-786c-4393-913c-3182eb2d7c9d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency.types false
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (a : ℕ) : 1 ≤ DirichletCharacter.zetaMul χ (p ^ (2 * a)) := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · simp only [h, zero_geom_sum]
    simp
  · simp only [h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : (1 : ℝ) ≤ ((2 * a + 1 : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    exact_mod_cast this
  · simp only [h, neg_one_geom_sum]
    have : ¬ Even (2 * a + 1) := by simp
    simp [this]
end Formalism.HermitianLattices.Ext.SupplyAP
