-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.area_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:03.283304+00:00
-- url     : https://prove2.me/submissions/751500c5-71c1-46aa-91f0-a637646c457b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly

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
theorem _root_.solution : area (scalePair L c hc) = ‖c‖ ^ 2 * area L := by
  simp only [area]
  change |(conj (c * L.ω₁) * (c * L.ω₂)).im| = ‖c‖ ^ 2 * |(conj L.ω₁ * L.ω₂).im|
  have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e : conj (c * L.ω₁) * (c * L.ω₂) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (conj L.ω₁ * L.ω₂) := by
    rw [map_mul, hn]
    ring
  rw [e]
  first
    | rw [Complex.im_ofReal_mul]
    | simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [abs_mul, abs_of_nonneg (by positivity)]
end Formalism.L2.Th1.F.Homog
