-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_CX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:42.237202+00:00
-- url     : https://prove2.me/submissions/220c3dec-9f66-4eba-995b-2dab157263d0

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_single

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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) (r : ι → ℝ) (i : ι) {c : K} (hc : ‖c‖ ≤ 1) :
    WtGe pi r (r i) (MvPowerSeries.C c * MvPowerSeries.X i) := by
  classical
  intro n
  unfold MonoWtGe
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  split_ifs with h
  · subst h
    rw [mul_one, dot_single]
    simp only [Nat.cast_one, one_mul, sub_self, Real.rpow_zero]
    exact hc
  · rw [mul_zero, norm_zero]
    exact Real.rpow_nonneg h0.le _
end Formalism.DworkPowerSeriesWeights
