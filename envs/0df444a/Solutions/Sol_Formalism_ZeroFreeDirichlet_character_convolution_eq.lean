-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.character_convolution_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:44:11.459684+00:00
-- url     : https://prove2.me/submissions/bf9a664f-c708-4ba3-b6fe-207ad3d27614

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ConvolutionNonnegOfDivisors

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
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {N N' M : ℕ} (χ : DirichletCharacter ℂ N) (χ' : DirichletCharacter ℂ N')
    (ψ : DirichletCharacter ℂ M) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    (n : ℕ) :
    (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) * toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M))) n
      = χ' (n : ZMod N') * DirichletCharacter.zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) a *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)) b), DirichletCharacter.zetaMul,
    coe_zeta_mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hdvd : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hi0 : i ≠ 0 := (Nat.pos_of_mem_divisors hi).ne'
  have hni : n / i ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hi0)).ne'
  simp only [toArithmeticFunction, coe_mk, hi0, hni, if_false]
  rw [hψ i]
  calc χ' ((n / i : ℕ) : ZMod N') * (χ (i : ZMod N) * χ' (i : ZMod N'))
      = (χ' ((n / i : ℕ) : ZMod N') * χ' (i : ZMod N')) * χ (i : ZMod N) := by ring
    _ = χ' (n : ZMod N') * χ (i : ZMod N) := by
      rw [← map_mul, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
end Formalism.ZeroFreeDirichlet
