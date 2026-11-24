-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:34:06.715169+00:00
-- url     : https://prove2.me/submissions/d2a0b811-ffbe-4fc6-bdc2-6d1272d3ed1b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk3
namespace Formalism.L2.Th1.F.Hk3
theorem _root_.solution (hv : HkIntValue) {τ : ℂ} (hτ : τ.im ≠ 0) {s : ℝ} (hs : 0 < s) (n : ℤ) :
    (if n = 0 then 0 else hkInt τ s n) =
      ((|(n : ℝ)| ^ (-(1 + 2 * s)) *
        (|τ.im| ^ (-(1 + 2 * s)) * (hkJ (1 + s) - 2 * hkJ (2 + s))) : ℝ) : ℂ) := by
  split_ifs with h
  · subst h
    rw [Int.cast_zero, abs_zero, Real.zero_rpow (by linarith)]
    simp
  · rw [hv τ s n hτ hs h, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_assoc]
end Formalism.L2.Th1.F.Hk3
