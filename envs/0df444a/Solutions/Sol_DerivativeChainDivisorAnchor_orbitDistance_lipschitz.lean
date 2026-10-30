-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.orbitDistance_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:07:00.596162+00:00
-- url     : https://prove2.me/submissions/a8cc5f80-a277-4d0f-8480-3d32bc9833ee

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
    (R b : ℝ) (hb : b ≤ 1) : orbitDistance z R 1-orbitDistance z R b ≤ 1-b := by
  have hterm (i j : ι) : ‖(R:ℂ)*z i-z j‖ ≤ ‖(R:ℂ)*z i-(b:ℂ)*z j‖+(1-b) := by
    have h := norm_add_le ((R:ℂ)*z i-(b:ℂ)*z j) ((b:ℂ)*z j-z j)
    rw [sub_add_sub_cancel] at h
    have he : (b:ℂ)*z j-z j = ((b-1:ℝ):ℂ)*z j := by push_cast; ring
    rw [he, norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : b-1 ≤ 0)] at h
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (hterm i j) (by positivity :
        0 ≤ (1/(Fintype.card ι : ℝ))*(1/(Fintype.card ι : ℝ)))))
  have he : (∑ i : ι, ∑ j : ι, (1/(Fintype.card ι : ℝ))*(1/(Fintype.card ι : ℝ))*
      (‖(R:ℂ)*z i-(b:ℂ)*z j‖+(1-b))) = orbitDistance z R b + (1-b) := by
    simp only [mul_add, Finset.sum_add_distrib, orbitDistance, ← Finset.mul_sum,
      ← Finset.sum_mul, uniform_mass, one_mul, mul_one]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
    <;> ring
  rw [he] at hsum
  have hs : orbitDistance z R 1 ≤ orbitDistance z R b+(1-b) := by
    simpa only [orbitDistance, Complex.ofReal_one, one_mul] using hsum
  linarith
