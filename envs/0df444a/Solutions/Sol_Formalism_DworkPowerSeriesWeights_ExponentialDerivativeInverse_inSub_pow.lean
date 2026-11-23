-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:06.814623+00:00
-- url     : https://prove2.me/submissions/04b53eb1-c7a6-4652-851c-2cb1431e1c7a

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_mul

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
variable {K : Type u} [NormedField K] {ι : Type v} {K0 : Subfield K}
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {f : MvPowerSeries ι K} (hf : InSub K0 f) (k : ℕ) : InSub K0 (f ^ k) := by
  induction k with
  | zero => simpa using (inSub_one : InSub K0 (1 : MvPowerSeries ι K))
  | succ k ih => rw [pow_succ]; exact inSub_mul ih hf
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
