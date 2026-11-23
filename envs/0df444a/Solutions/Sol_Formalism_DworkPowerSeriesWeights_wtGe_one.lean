-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:32.035866+00:00
-- url     : https://prove2.me/submissions/5609a20b-1705-4fb5-8ae7-75a5c4457e60

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_zero

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
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) (r : ι → ℝ) : WtGe pi r 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  rw [monoWtGe_iff, MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp [dot_zero]
  · simpa using Real.rpow_nonneg h0.le _
end Formalism.DworkPowerSeriesWeights
