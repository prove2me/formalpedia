-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.herm_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:35.818803+00:00
-- url     : https://prove2.me/submissions/f0a73e97-9f32-4ad1-9501-530434cf711c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_area_scale
import Theorems.Thm_Formalism_L2_Th1_F_areaPos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
namespace Formalism.L2.Th1.F.Homog
theorem _root_.solution (z w : ℂ) : herm (scalePair L c hc) (c * z) (c * w) = herm L z w := by
  simp only [herm, area_scale L c hc]
  have hA : (area L : ℂ) ≠ 0 := by exact_mod_cast (areaPos L).ne'
  have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
  have hn : ((‖c‖ ^ 2 * area L : ℝ) : ℂ) = c * conj c * (area L : ℂ) := by
    rw [Complex.ofReal_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn, map_mul, div_eq_div_iff (mul_ne_zero (mul_ne_zero hc hcc) hA) hA]
  ring
end Formalism.L2.Th1.F.Homog
