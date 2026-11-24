-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.tsum_abs_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:14.251374+00:00
-- url     : https://prove2.me/submissions/9405aaf9-f705-4dcf-8a21-35729612d225

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


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
theorem _root_.solution {b : ℝ} (hb : 1 < b) :
    ∑' n : ℤ, |(n : ℝ)| ^ (-b) = 2 * ∑' n : ℕ, 1 / (n : ℝ) ^ b := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ b) := Real.summable_one_div_nat_rpow.mpr hb
  have e1 : (fun n : ℕ => |((n : ℤ) : ℝ)| ^ (-b)) = fun n : ℕ => 1 / (n : ℝ) ^ b := by
    ext n
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n), Real.rpow_neg (Nat.cast_nonneg n),
      one_div]
  have e2 : (fun n : ℕ => |((-(n : ℤ) : ℤ) : ℝ)| ^ (-b)) = fun n : ℕ => 1 / (n : ℝ) ^ b := by
    ext n
    rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n),
      Real.rpow_neg (Nat.cast_nonneg n), one_div]
  rw [Summable.tsum_of_nat_of_neg (f := fun n : ℤ => |(n : ℝ)| ^ (-b)) (by rw [e1]; exact hs)
    (by rw [e2]; exact hs), e1, e2, Int.cast_zero, abs_zero, Real.zero_rpow (by linarith)]
  ring
end Formalism.L2.Th1.F.Hk3
