-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.le_rpow_of_forall_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:31.69923+00:00
-- url     : https://prove2.me/submissions/97688b3d-321f-4039-ab77-698be6540811

import Definitions.Def_Formalism_GaussJetBounds_StatementV
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAMatrixEntries
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_l_pos
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_l_lt_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_exists_norm_eq_rpow_rat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] (b x : ℝ) (hx : 0 ≤ x)
    (h : ∀ c : ℂ_[l], ‖(l : ℂ_[l])‖ ^ b ≤ ‖c‖ → x ≤ ‖c‖) : x ≤ ‖(l : ℂ_[l])‖ ^ b := by
  have hπ := norm_l_pos l
  have hπ1 := norm_l_lt_one l
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0]; exact Real.rpow_nonneg hπ.le _
  by_contra hlt
  rw [not_le] at hlt
  set t : ℝ := Real.logb ‖(l : ℂ_[l])‖ x with ht
  have hxt : ‖(l : ℂ_[l])‖ ^ t = x := Real.rpow_logb hπ hπ1.ne h0
  rw [← hxt] at hlt
  have htb : t < b := (Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ hπ1).1 hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn htb
  obtain ⟨c, hc⟩ := exists_norm_eq_rpow_rat l q
  have h1 : x ≤ ‖c‖ := h c (by
    rw [hc]; exact Real.rpow_le_rpow_of_exponent_ge hπ hπ1.le hq2.le)
  rw [hc, ← hxt] at h1
  exact absurd h1 (not_le.2 ((Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ hπ1).2 hq1))
end Formalism.DworkPowerSeriesWeights
