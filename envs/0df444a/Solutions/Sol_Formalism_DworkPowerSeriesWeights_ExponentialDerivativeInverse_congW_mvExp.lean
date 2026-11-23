-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:55.493282+00:00
-- url     : https://prove2.me/submissions/aa6b67c7-d86b-42a0-ad10-45c7beb47c71

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_exists_ne_zero_of_finsum_ne_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_congW_pow

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
theorem _root_.solution [CharZero K] {D : MvPowerSeries ι K}
    (hD0 : MvPowerSeries.constantCoeff D = 0) (hD : CongW N w D) : CongW N w (mvExp D) := by
  intro n hn
  unfold mvExp at hn
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hD0)] at hn
  obtain ⟨k, hk⟩ := exists_ne_zero_of_finsum_ne_zero hn
  simp only [smul_eq_mul] at hk
  exact congW_pow hD k n (right_ne_zero_of_mul hk)
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
