-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.good_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:46.33427+00:00
-- url     : https://prove2.me/submissions/b82d8ef5-4529-4680-8afb-08985b34ce36

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_sub
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_congW_sub

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
variable {K : Type u} [NormedField K] {d : ℕ}
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {K0 : Subfield K} {N : ℤ} {w : V2 d → ℤ} {f g : MvPowerSeries (V2 d) K}
    (hf : Good K0 N w f) (hg : Good K0 N w g) : Good K0 N w (f - g) :=
  ⟨by rw [map_sub, hf.1, hg.1, sub_zero], inSub_sub hf.2.1 hg.2.1, congW_sub hf.2.2 hg.2.2⟩
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
