-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.orbitDistance_monotone_unit
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:49:51.512606+00:00
-- url     : https://prove2.me/submissions/8e18cf0b-5630-4619-bb7a-a46453e4d84b

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorOrbitEstimates
import Theorems.Thm_DerivativeChainDivisorAnchor_orbitDistance_lower
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
open scoped BigOperators
open DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
noncomputable section
variable {ι : Type} [Fintype ι] [Nonempty ι]



theorem uniform_mass : (∑ i : ι, (1/(Fintype.card ι : ℝ))) = 1 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp


















end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open DerivativeChainContinuation
open DerivativeChainDivisorAnchor

variable {ι : Type} [Fintype ι] [Nonempty ι]















theorem solution (z : ι → ℂ) (hz : ∀ i, ‖z i‖=1)
    (hm : ∑ i, z i=0) (R b : ℝ) (hR : 0 ≤ R) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    orbitDistance z R b ≤ orbitDistance z R 1 := by
  have hterm (i j : ι) : ‖(R:ℂ)*z i-(b:ℂ)*z j‖ ≤
      (1-b)*‖(R:ℂ)*z i‖ + b*‖(R:ℂ)*z i-z j‖ := by
    have he : (R:ℂ)*z i-(b:ℂ)*z j = ((1-b:ℝ):ℂ)*((R:ℂ)*z i) +
        (b:ℂ)*((R:ℂ)*z i-z j) := by push_cast; ring
    rw [he]
    exact (norm_add_le _ _).trans_eq (by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb,
        abs_of_nonneg (by linarith : 0 ≤ 1-b)])
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (hterm i j) (by positivity :
        0 ≤ (1/(Fintype.card ι : ℝ))*(1/(Fintype.card ι : ℝ)))))
  have he : (∑ i : ι, ∑ j : ι, (1/(Fintype.card ι : ℝ))*(1/(Fintype.card ι : ℝ))*
      ((1-b)*‖(R:ℂ)*z i‖+b*‖(R:ℂ)*z i-z j‖)) =
      (1-b)*R+b*orbitDistance z R 1 := by
    simp only [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR,
      orbitDistance, Complex.ofReal_one, one_mul, mul_add, Finset.sum_add_distrib]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, uniform_mass, one_mul, mul_one]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
    <;> ring
  rw [he] at hsum
  have hs : orbitDistance z R b ≤ (1-b)*R+b*orbitDistance z R 1 := by
    simpa only [orbitDistance, Complex.ofReal_one, one_mul] using hsum
  have hl := orbitDistance_lower z hz hm R 1 hR
  nlinarith
