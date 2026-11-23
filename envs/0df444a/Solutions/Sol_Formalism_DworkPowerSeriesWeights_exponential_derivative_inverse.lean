-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.exponential_derivative_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:22.490318+00:00
-- url     : https://prove2.me/submissions/d1ad3ef3-fbeb-4af8-9c26-c6b0ac4a022f

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_mvExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_congW_mvExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_congW_of_torus
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_good_sub
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_good_subst
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_zero_series_family
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_oddIndicator_alt_series_family
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_swappedParity_series_family
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_oddIndicator_series_family
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_parityIndicator_series_family
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260


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
open ExponentialDerivativeInverse
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ExpDeInv.{u} := by
  intro K _ _ l d _ hl hd _ K0 ζ hζ be hK0 htor hcc D hD
  have hN : l ^ d - 1 ≠ 0 := by
    have h2 : 2 ≤ l ^ d := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
    omega
  have hcb := congW_of_torus hN hζ htor
  have hD' : Good K0 ((l ^ d - 1 : ℕ) : ℤ) (fun x : V2 d => lw l x.2) D := by
    rcases hD with rfl | rfl
    · exact good_sub (good_sub (good_subst hK0 hcc hcb oddIndicator_alt_series_family) (good_subst hK0 hcc hcb zero_series_family))
        (good_subst hK0 hcc hcb swappedParity_series_family)
    · exact good_sub (good_sub (good_subst hK0 hcc hcb oddIndicator_series_family) (good_subst hK0 hcc hcb zero_series_family))
        (good_subst hK0 hcc hcb parityIndicator_series_family)
  exact ⟨inSub_mvExp hD'.1 hD'.2.1, fun n hn => congW_mvExp hD'.1 hD'.2.2 n hn⟩
end Formalism.DworkPowerSeriesWeights
