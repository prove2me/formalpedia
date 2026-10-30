-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.orbitDistance_lower
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:48:13.669705+00:00
-- url     : https://prove2.me/submissions/a45ec1ff-8dc4-49df-9cbf-504575647795

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorOrbitEstimates
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

theorem finite_norm_mean_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i, 0 ≤ w i) :
    ‖∑ i, (w i : ℂ)*z i‖ ≤ ∑ i, w i*‖z i‖ := by
  calc
    _ ≤ ∑ i, ‖(w i : ℂ)*z i‖ := norm_sum_le _ _
    _ = _ := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)]

theorem finite_distance_mean_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) (b x : ℂ)
    (hm : ∑ i, (w i : ℂ)*z i=b) :
    ‖x-b‖ ≤ ∑ i, w i*‖x-z i‖ := by
  have he : (∑ i, (w i:ℂ)*(x-z i))=x-b := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, hs, hm]
    simp
  simpa only [he] using finite_norm_mean_le w (fun i => x-z i) hw








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
    (hm : ∑ i, z i=0) (R S : ℝ) (hR : 0 ≤ R) : R ≤ orbitDistance z R S := by
  have hmean : (∑ j, ((1/(Fintype.card ι : ℝ) : ℝ):ℂ)*((S:ℂ)*z j)) = 0 := by
    simp only [← Finset.mul_sum, hm, mul_zero]
  have hrow (i : ι) : R ≤ ∑ j, (1/(Fintype.card ι : ℝ))*‖(R:ℂ)*z i-(S:ℂ)*z j‖ := by
    have h := finite_distance_mean_le (fun _ : ι => (1/(Fintype.card ι : ℝ)))
      (fun j => (S:ℂ)*z j) (fun _ => by positivity) uniform_mass 0 ((R:ℂ)*z i) hmean
    simpa [norm_mul, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR] using h
  calc
    R = ∑ i : ι, (1/(Fintype.card ι : ℝ))*R := by rw [← Finset.sum_mul, uniform_mass, one_mul]
    _ ≤ ∑ i, (1/(Fintype.card ι : ℝ))*(∑ j, (1/(Fintype.card ι : ℝ))*‖(R:ℂ)*z i-(S:ℂ)*z j‖) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (by positivity)
    _ = _ := by simp only [orbitDistance, Finset.mul_sum, mul_assoc]
