-- Prove2me | solution 1 for Formalism.ELL.N_partial_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:07.353952+00:00
-- url     : https://prove2.me/submissions/adabc2a9-f5d8-449b-8020-4a9acef3f656

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_pderiv_subst
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_mul
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_pderiv
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_subst

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
open Formalism Formalism.ELL
namespace Formalism.ELL
theorem _root_.solution : NPderiv := by
  intro K _ _ _ σ G hG i
  obtain ⟨f, hf0, hf, rfl⟩ := hG
  unfold logOnePlus
  rw [SubstitutionCoefficientCongruence.pderiv_subst _ hf0]
  refine SubstitutionCoefficientCongruence.integral_mul ?_ (SubstitutionCoefficientCongruence.integral_pderiv hf i)
  refine SubstitutionCoefficientCongruence.integral_subst ?_ hf0 hf
  intro n
  unfold PowerSeries.log
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n)]
  have hn : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [map_div₀, map_pow, map_neg, map_one, map_natCast, Nat.cast_succ, div_mul_cancel₀ _ hn,
    norm_pow, norm_neg, norm_one, one_pow]
end Formalism.ELL
