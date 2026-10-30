-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.orbit_cross_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:09:14.745586+00:00
-- url     : https://prove2.me/submissions/2f5330a1-07a3-410a-84e7-2e0b7f16d581

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorOrbitEstimates
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
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
namespace DerivativeChainContinuation
open scoped BigOperators



theorem finite_weighted_square_bound {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    (∑ i, w i*f i)^2 ≤ ∑ i, w i*(f i)^2 := by
  have h1 (i : ι) : Real.sqrt (w i)*(Real.sqrt (w i)*f i)=w i*f i := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (hw i)]
  have h2 (i : ι) : (Real.sqrt (w i)*f i)^2=w i*(f i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i)*f i)
  simpa only [h1,h2,Real.sq_sqrt (hw _),hs,one_mul] using hh



end DerivativeChainContinuation


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
    (hm : ∑ i, z i=0) (a : ℝ) : orbitDistance z 1 a ≤ 1+a^2/2 := by
  have hmean : (∑ j, ((1/(Fintype.card ι : ℝ):ℝ):ℂ)*((a:ℂ)*z j)) = 0 := by
    simp only [← Finset.mul_sum, hm, mul_zero]
  have hrow (i : ι) :
      (∑ j, (1/(Fintype.card ι : ℝ))*‖z i-(a:ℂ)*z j‖) ≤ 1+a^2/2 := by
    have hv := finite_weighted_variance (fun _ : ι => (1/(Fintype.card ι : ℝ)))
      (fun j => (a:ℂ)*z j) 0 (z i) uniform_mass hmean
    have he : (∑ j, (1/(Fintype.card ι : ℝ))*‖z i-(a:ℂ)*z j‖^2) = 1+a^2 := by
      calc
        _ = ∑ j, (1/(Fintype.card ι : ℝ))*‖(a:ℂ)*z j-z i‖^2 := by simp_rw [norm_sub_rev]
        _ = _ := by
          rw [hv]
          simp only [zero_sub, sub_zero, norm_neg, norm_mul, hz, one_pow, mul_one,
            Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Finset.sum_mul, uniform_mass, one_mul]
    have hsq := finite_weighted_square_bound (fun _ : ι => (1/(Fintype.card ι : ℝ)))
      (fun j => ‖z i-(a:ℂ)*z j‖) (fun _ => by positivity) uniform_mass
    rw [he] at hsq
    have hn : 0 ≤ ∑ j, (1/(Fintype.card ι : ℝ))*‖z i-(a:ℂ)*z j‖ := by positivity
    nlinarith [sq_nonneg (a^2)]
  calc
    _ = ∑ i, (1/(Fintype.card ι : ℝ))*(∑ j, (1/(Fintype.card ι : ℝ))*‖z i-(a:ℂ)*z j‖) := by
      simp only [orbitDistance, Complex.ofReal_one, one_mul, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i : ι, (1/(Fintype.card ι : ℝ))*(1+a^2/2) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, uniform_mass, one_mul]
