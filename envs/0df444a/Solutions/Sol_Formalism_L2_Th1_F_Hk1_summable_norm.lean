-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk1.summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:46:06.137902+00:00
-- url     : https://prove2.me/submissions/2b06e08e-8254-42fc-b6bc-f0627e3ae983

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelIntegralValue
import Theorems.Thm_Formalism_L2_Th1_F_Hk1_summable_upper

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
open MeasureTheory Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk1
namespace Formalism.L2.Th1.F.Hk1
theorem _root_.solution (τ : ℂ) (s : ℝ) (hτ : τ.im ≠ 0) (hs : 0 < s) :
    Summable (fun p : ℤ × ℤ => ‖(p.1 : ℂ) + (p.2 : ℂ) * τ‖ ^ (-(2 + 2 * s))) := by
  rcases lt_or_gt_of_ne hτ with h | h
  · have h' : 0 < (conj τ).im := by simpa using h
    refine (summable_upper ⟨conj τ, h'⟩ s hs).congr (fun p => ?_)
    have : (p.1 : ℂ) + (p.2 : ℂ) * conj τ = conj ((p.1 : ℂ) + (p.2 : ℂ) * τ) := by simp
    show ‖(p.1 : ℂ) + (p.2 : ℂ) * conj τ‖ ^ _ = _
    rw [this, Complex.norm_conj]
  · exact summable_upper ⟨τ, h⟩ s hs
end Formalism.L2.Th1.F.Hk1
