-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:44.137618+00:00
-- url     : https://prove2.me/submissions/138ef242-4d92-4f79-8b48-1d2e67771714

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_add

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
theorem _root_.solution {f g : MvPowerSeries ι K} (hf : CongW N w f) (hg : CongW N w g) :
    CongW N w (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, wsum_add]
  exact dvd_add (hf p.1 (left_ne_zero_of_mul hpn)) (hg p.2 (right_ne_zero_of_mul hpn))
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
