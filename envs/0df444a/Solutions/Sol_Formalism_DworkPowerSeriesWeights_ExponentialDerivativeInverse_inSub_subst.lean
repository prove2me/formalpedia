-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:46.425542+00:00
-- url     : https://prove2.me/submissions/b57de748-b683-489f-b46a-fc1dd9e454ae

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_prod
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
theorem _root_.solution {σ : Type w} [Finite σ] {a : σ → MvPowerSeries ι K}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, InSub K0 (a s))
    {f : MvPowerSeries σ K} (hf : InSub K0 f) : InSub K0 (MvPowerSeries.subst a f) := by
  intro n
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]
  refine finsum_mem_sub _ fun m => ?_
  rw [smul_eq_mul]
  exact K0.mul_mem (hf m) (inSub_prod m.support _ (fun s _ => inSub_pow (ha s) _) n)
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
