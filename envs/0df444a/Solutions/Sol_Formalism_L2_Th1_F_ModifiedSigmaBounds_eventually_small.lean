-- Prove2me | solution 1 for Formalism.L2.Th1.F.ModifiedSigmaBounds.eventually_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:25:05.62509+00:00
-- url     : https://prove2.me/submissions/880bc05b-6204-467d-b9c3-90c288e3d875

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
import Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_eventually_large


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
theorem _root_.solution (L : PeriodPair) :
    ∀ᶠ z : ℂ in nhds 0, ∀ l : L.lattice, (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖ := by
  have hlim : Tendsto (fun z : ℂ => 2 * ‖z‖) (nhds 0) (nhds 0) := by
    have hc : Continuous fun z : ℂ => 2 * ‖z‖ := by fun_prop
    simpa using hc.tendsto 0
  have hfin : {l : L.lattice | ¬ (1 : ℝ) ≤ ‖(l : ℂ)‖}.Finite := eventually_large L 1
  have h1 : ∀ᶠ z : ℂ in nhds 0, ∀ l ∈ {l : L.lattice | ¬ (1 : ℝ) ≤ ‖(l : ℂ)‖},
      (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖ := by
    rw [Filter.eventually_all_finite hfin]
    intro l _
    by_cases hl : (l : ℂ) = 0
    · simp [hl]
    · filter_upwards [hlim.eventually_le_const (norm_pos_iff.mpr hl)] with z hz _ using hz
  have h2 : ∀ᶠ z : ℂ in nhds 0, 2 * ‖z‖ ≤ 1 := hlim.eventually_le_const one_pos
  filter_upwards [h1, h2] with z hz1 hz2 l hl
  by_cases h : 1 ≤ ‖(l : ℂ)‖
  · exact hz2.trans h
  · exact hz1 l h hl
end Formalism.L2.Th1.F.ModifiedSigmaBounds
