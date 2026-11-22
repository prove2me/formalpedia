-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:01.435098+00:00
-- url     : https://prove2.me/submissions/89235b35-a81f-49c9-a69b-fe824bd12866

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_add

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
variable [IsUltrametricDist K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {w1 w2 : ℝ}
    {f g : MvPowerSeries ι K} (hf : WtGe pi r w1 f) (hg : WtGe pi r w2 g) :
    WtGe pi r (w1 + w2) (f * g) := by
  classical
  intro n
  rw [monoWtGe_iff, MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
    fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [norm_mul, ← hx, dot_add]
  calc ‖MvPowerSeries.coeff x.1 f‖ * ‖MvPowerSeries.coeff x.2 g‖
      ≤ pi ^ (w1 - dot x.1 r) * pi ^ (w2 - dot x.2 r) :=
        mul_le_mul (hf x.1) (hg x.2) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (w1 + w2 - (dot x.1 r + dot x.2 r)) := by
        rw [← Real.rpow_add h0]; congr 1; ring
end Formalism.DworkPowerSeriesWeights
