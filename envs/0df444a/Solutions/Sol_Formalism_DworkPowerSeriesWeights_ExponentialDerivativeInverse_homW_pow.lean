-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.homW_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:12.401072+00:00
-- url     : https://prove2.me/submissions/4d597e57-0245-4349-bd44-0d52119aa099

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_homW_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_homW_mul

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
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {c : ℤ} {f : MvPowerSeries ι K} (hf : HomW w c f) (k : ℕ) :
    HomW w (k * c) (f ^ k) := by
  induction k with
  | zero => intro n hn; simpa using homW_one n (by simpa using hn)
  | succ k ih =>
    rw [pow_succ]
    intro n hn
    rw [homW_mul ih hf n hn]
    push_cast; ring
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
