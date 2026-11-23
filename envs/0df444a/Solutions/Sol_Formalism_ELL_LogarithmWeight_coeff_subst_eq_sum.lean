-- Prove2me | solution 1 for Formalism.ELL.LogarithmWeight.coeff_subst_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:57.473999+00:00
-- url     : https://prove2.me/submissions/b4896dfe-5240-48ab-bad5-952b1158d445

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
import Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_pow_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.LogarithmWeight
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.LogarithmWeight
theorem _root_.solution {l e : PowerSeries K} (he : constantCoeff e = 0) (n : ℕ) :
    coeff n (l.subst e) = ∑ m ∈ Finset.range (n + 1), coeff m l * coeff n (e ^ m) := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' he)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) ?_]
  · simp [smul_eq_mul]
  · intro m hm
    simp only [Function.mem_support] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hm
    rw [coeff_pow_eq_zero he (by omega), smul_zero]
end Formalism.ELL.LogarithmWeight
