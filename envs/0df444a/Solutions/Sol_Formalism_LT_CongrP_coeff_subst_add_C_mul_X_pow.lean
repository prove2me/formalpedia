-- Prove2me | solution 1 for Formalism.LT.CongrP.coeff_subst_add_C_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:21.447233+00:00
-- url     : https://prove2.me/submissions/dfe40934-8701-4922-9de8-230a225621a7

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
import Theorems.Thm_Formalism_LT_CongrP_coeff_subst_range
import Theorems.Thm_Formalism_LT_CongrP_sum_zero_pow_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {R : Type*} [CommRing R]
namespace Formalism.LT.CongrP
theorem _root_.solution (f b : PowerSeries R) (hb : constantCoeff b = 0) (c : R)
    {N : ℕ} (hN : 1 ≤ N) :
    coeff N (f.subst (b + C c * X ^ N)) = coeff N (f.subst b) + coeff 1 f * c := by
  have he : constantCoeff (C c * X ^ N : PowerSeries R) = 0 := by
    rw [map_mul, map_pow, constantCoeff_X, zero_pow (by omega), mul_zero]
  have hbe : constantCoeff (b + C c * X ^ N) = 0 := by rw [map_add, hb, he, add_zero]
  have key : ∀ n : ℕ, coeff N ((b + C c * X ^ N) ^ n) = coeff N (b ^ n) + if n = 1 then c else 0 := by
    intro n
    have hg := geom_sum₂_mul (b + C c * X ^ N) b n
    have hx : (b + C c * X ^ N) ^ n = b ^ n + X ^ N * (C c * ∑ i ∈ Finset.range n,
        (b + C c * X ^ N) ^ i * b ^ (n - 1 - i)) := by
      rw [← sub_eq_iff_eq_add', ← hg]
      ring
    rw [hx, map_add, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_C, map_sum]
    simp only [map_mul, map_pow, hbe, hb]
    rw [sum_zero_pow_mul]
    split_ifs <;> simp
  rw [coeff_subst_range f _ hbe, coeff_subst_range f b hb]
  simp_rw [key, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  congr 1
  rw [Finset.sum_eq_single 1]
  · simp
  · intro n _ hn; simp [hn]
  · intro h; exfalso; apply h; simp; omega
end Formalism.LT.CongrP
