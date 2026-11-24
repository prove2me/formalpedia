-- Prove2me | solution 1 for Formalism.L2.Th1.F.ModifiedSigmaBounds.sigma_sub_id_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:07:42.519852+00:00
-- url     : https://prove2.me/submissions/1f56c66b-2030-40fd-be5a-f9b5ede50b92

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
import Theorems.Thm_Formalism_L2_Th1_F_ModifiedSigmaBounds_eventually_small
import Theorems.Thm_Formalism_L2_Th1_F_ModifiedSigmaBounds_norm_tprod_sub_one_le

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
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds
open Formalism.L2.Th1.F.ModifiedSigmaBounds
open SigmaConv
namespace Formalism.L2.Th1.F.ModifiedSigmaBounds
theorem _root_.solution (hs : SigmaSummable) (L : PeriodPair) :
    ∃ K r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → ‖wSigma L z - z‖ ≤ K * ‖z‖ ^ 4 := by
  set C : ℝ := ∑' l : L.lattice, ‖l‖ ^ (-3 : ℝ) with hC
  have hC0 : 0 ≤ C := tsum_nonneg fun l => by positivity
  have hlim : Tendsto (fun z : ℂ => 2 * ‖z‖ ^ 3 * C) (nhds 0) (nhds 0) := by
    have : Continuous fun z : ℂ => 2 * ‖z‖ ^ 3 * C := by fun_prop
    simpa using this.tendsto 0
  have hev := (eventually_small L).and (hlim.eventually_le_const one_pos)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨4 * C, r, hr, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hball (by simpa using hz)
  have hb := norm_tprod_sub_one_le hs L z h1
  rw [tsum_mul_left, ← hC] at hb
  have hx0 : 0 ≤ 2 * ‖z‖ ^ 3 * C := by positivity
  have hexp := Real.abs_exp_sub_one_le (x := 2 * ‖z‖ ^ 3 * C) (by rwa [abs_of_nonneg hx0])
  rw [abs_of_nonneg hx0] at hexp
  have hexp' := (le_abs_self _).trans hexp
  have heq : wSigma L z - z = z * (∏' l : L.lattice, wFactor (l : ℂ) z - 1) := by
    simp only [wSigma]; ring
  rw [heq, norm_mul]
  calc ‖z‖ * ‖∏' l : L.lattice, wFactor (l : ℂ) z - 1‖
      ≤ ‖z‖ * (2 * (2 * ‖z‖ ^ 3 * C)) := by
        gcongr
        exact hb.trans hexp'
    _ = 4 * C * ‖z‖ ^ 4 := by ring
end Formalism.L2.Th1.F.ModifiedSigmaBounds
