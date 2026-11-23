-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:06.4553+00:00
-- url     : https://prove2.me/submissions/718b6c61-85a7-4acf-9fc5-737eec0ab79a

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_finsum_mem_sub

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
theorem _root_.solution [CharZero K] {D : MvPowerSeries ι K}
    (hD0 : MvPowerSeries.constantCoeff D = 0) (hD : InSub K0 D) : InSub K0 (mvExp D) := by
  intro n
  unfold mvExp
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hD0)]
  refine finsum_mem_sub _ fun k => ?_
  rw [smul_eq_mul, PowerSeries.coeff_exp]
  have hq : algebraMap ℚ K (1 / (k.factorial : ℚ)) ∈ K0 := by
    rw [map_div₀, map_one, map_natCast]
    exact K0.div_mem K0.one_mem (natCast_mem K0 _)
  exact K0.mul_mem hq (inSub_pow hD k n)
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
