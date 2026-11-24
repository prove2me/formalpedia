-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.prime_power_coefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:46.136305+00:00
-- url     : https://prove2.me/submissions/36a23831-c850-4914-a392-1a6cdb1ce7ce

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ConvolutionNonnegOfDivisors
import Theorems.Thm_Formalism_ZeroFreeDirichlet_convolution_nonneg_of_divisors
import Theorems.Thm_Formalism_ZeroFreeDirichlet_character_convolution_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
set_option backward.isDefEq.respectTransparency.types false
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {N N' M : ℕ} {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ N'}
    {ψ : DirichletCharacter ℂ M} (hχ : χ ^ 2 = 1) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    {p : ℕ} (hp : p.Prime)
    (hc : χ' (p : ZMod N') = 0 ∨ χ' (p : ZMod N') = 1 ∨ (χ' (p : ZMod N') = -1 ∧ χ (p : ZMod N) = -1))
    (k : ℕ) :
    0 ≤ (DirichletCharacter.zetaMul χ * (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)))) (p ^ k) := by
  have hζ : ∀ j, DirichletCharacter.zetaMul χ (p ^ j) = ∑ i ∈ Finset.range (j + 1), χ (p : ZMod N) ^ i := by
    intro j
    rw [DirichletCharacter.zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [toArithmeticFunction, hp.ne_zero]
  apply convolution_nonneg_of_divisors
  · intro d _
    exact DirichletCharacter.zetaMul_nonneg hχ d
  · intro d hd
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [character_convolution_eq χ χ' ψ hψ, Nat.cast_pow, map_pow]
    rcases hc with h | h | ⟨h, h'⟩
    · exact mul_nonneg (by rw [h]; exact pow_nonneg le_rfl j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · exact mul_nonneg (by rw [h]; exact pow_nonneg zero_le_one j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · rw [h, hζ, h', neg_one_geom_sum]
      split_ifs with he
      · simp
      · have hj : Even j := by
          rcases Nat.even_or_odd j with hj | hj
          · exact hj
          · exact absurd hj.add_one he
        rw [hj.neg_one_pow]
        norm_num
end Formalism.ZeroFreeDirichlet
