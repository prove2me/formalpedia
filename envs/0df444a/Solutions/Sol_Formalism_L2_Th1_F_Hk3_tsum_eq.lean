-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.tsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:51:54.809564+00:00
-- url     : https://prove2.me/submissions/1436d9bb-37db-403d-bd4b-954a4a99fb3b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_tsum_abs_int
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_term_eq
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_K_eq
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
theorem _root_.solution (hv : HkIntValue) (hj : HkJRules) {τ : ℂ} (hτ : τ.im ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∑' n : ℤ, if n = 0 then 0 else hkInt τ s n) =
      (((((1 + 2 * s) - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * s)) *
        (|τ.im| ^ (-(1 + 2 * s)) * (-(1 / (s + 1)) * hkJ (1 + s))) : ℝ) : ℂ) := by
  simp_rw [term_eq hv hτ hs]
  rw [← Complex.ofReal_tsum, tsum_mul_right, tsum_abs_int (by linarith), K_eq hj hs]
  congr 1
  ring
end Formalism.L2.Th1.F.Hk3
