-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:11.021919+00:00
-- url     : https://prove2.me/submissions/7764b3e0-a1e0-4365-aa9a-a893b95c685d

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_mul

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
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {f : MvPowerSeries ι K}
    (hf : WtGe pi r wt f) (k : ℕ) : WtGe pi r (k * wt) (f ^ k) := by
  induction k with
  | zero => simpa using wtGe_one (K := K) h0 r
  | succ k ih =>
    rw [pow_succ]
    have := wtGe_mul h0 ih hf
    push_cast
    rwa [add_mul, one_mul]
end Formalism.DworkPowerSeriesWeights
