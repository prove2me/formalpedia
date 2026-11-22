-- Prove2me | solution 1 for Formalism.LT.CongrP.coeff_subst_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:51.391844+00:00
-- url     : https://prove2.me/submissions/934e94a2-1a49-4efe-ba38-9111e6bf6b3d

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow

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
theorem _root_.solution (f a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    coeff N (f.subst a) = ∑ n ∈ Finset.range (N + 1), coeff n f * coeff N (a ^ n) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' ha)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1))]
  · simp [smul_eq_mul]
  · intro n hn
    simp only [Function.mem_support] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    obtain ⟨b, rfl⟩ := X_dvd_iff.mpr ha
    rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]
end Formalism.LT.CongrP
