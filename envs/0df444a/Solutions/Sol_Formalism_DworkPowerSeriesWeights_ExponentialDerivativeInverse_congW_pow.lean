-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:42.868153+00:00
-- url     : https://prove2.me/submissions/7c4fe5b0-91c1-4c7b-9d3f-949bb7ee83fe

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_congW_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_congW_mul

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
open Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
variable {K : Type u} [NormedField K] {ι : Type v}
variable {w : ι → ℤ}
variable {N : ℤ}
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {f : MvPowerSeries ι K} (hf : CongW N w f) (k : ℕ) : CongW N w (f ^ k) := by
  induction k with
  | zero => simpa using (congW_one : CongW N w (1 : MvPowerSeries ι K))
  | succ k ih => rw [pow_succ]; exact congW_mul ih hf
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
