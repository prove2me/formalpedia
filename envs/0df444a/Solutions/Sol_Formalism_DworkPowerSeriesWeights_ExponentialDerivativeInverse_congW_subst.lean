-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:43.141604+00:00
-- url     : https://prove2.me/submissions/9bab4829-7116-4f8f-82c8-aeb57d5e6438

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_exists_ne_zero_of_finsum_ne_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_homW_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_homW_prod

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
theorem _root_.solution {σ : Type w} [Finite σ] {w1 : σ → ℤ} {a : σ → MvPowerSeries ι K}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, HomW w (w1 s) (a s))
    {f : MvPowerSeries σ K} (hf : CongW N w1 f) : CongW N w (MvPowerSeries.subst a f) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)] at hn
  obtain ⟨m, hm⟩ := exists_ne_zero_of_finsum_ne_zero hn
  simp only [smul_eq_mul] at hm
  have h1 := hf m (left_ne_zero_of_mul hm)
  have h2 := homW_prod m.support (fun s => (m s : ℤ) * w1 s) (fun s => a s ^ m s)
    (fun s _ => homW_pow (ha s) (m s)) n (right_ne_zero_of_mul hm)
  rw [h2]
  exact h1
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
