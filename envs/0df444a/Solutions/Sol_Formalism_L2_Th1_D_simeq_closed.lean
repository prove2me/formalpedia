-- Prove2me | solution 1 for Formalism.L2.Th1.D.simeq_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:04:14.059328+00:00
-- url     : https://prove2.me/submissions/45360ccc-f68c-40ec-9715-9cf07ea7f4c8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Theorems.Thm_Formalism_L2_Th1_D_sigma_isometry
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_dworkMv
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_of_not_dvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_smul
import Theorems.Thm_Formalism_LT_InvIntP_Low_sub


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open TraceNormBounds
namespace Formalism.L2.Th1.D
theorem _root_.solution : SimeqClosed := by
  intro K _ _ _ l σ hU τ _ f g hlim hf
  have hiso := sigma_isometry K l σ hU
  obtain ⟨hp, hp2, hpn, hval, hσ⟩ := hU
  have hp0 : l ≠ 0 := hp.ne_zero
  have hD := Formalism.InvariantFactorPaths.G7.Top.dworkMv
  have hcont : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hiso).continuous
  have hf0 : ∀ k, MvPowerSeries.constantCoeff (f k) = 0 := fun k => by
    have := (hf k).1
    rwa [sub_zero] at this
  have hg0 : MvPowerSeries.constantCoeff g = 0 := by
    have h := hlim 0
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨by rwa [sub_zero], ?_⟩
  rw [sub_zero, hD K τ l σ hp hpn hσ _ hg0]
  intro n
  have hk : ∀ k, ‖MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ (f k)) -
      MvPowerSeries.C (l : K) * f k)‖ ≤ (l : ℝ)⁻¹ := fun k =>
    (hD K τ l σ hp hpn hσ _ (hf0 k)).1 (by have := (hf k).2; rwa [sub_zero] at this) n
  have hT : Filter.Tendsto (fun k => MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ (f k)) -
      MvPowerSeries.C (l : K) * f k)) Filter.atTop
      (nhds (MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ g) -
        MvPowerSeries.C (l : K) * g))) := by
    simp only [map_sub, MvPowerSeries.coeff_C_mul]
    refine Filter.Tendsto.sub ?_ ((hlim n).const_mul _)
    by_cases hd : ∀ i, l ∣ n i
    · obtain ⟨m, rfl⟩ : ∃ m : τ →₀ ℕ, n = l • m := by
        refine ⟨n.mapRange (· / l) (by simp), ?_⟩
        ext i
        simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
        exact (Nat.mul_div_cancel' (hd i)).symm
      simp only [Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul hp0, MvPowerSeries.coeff_map]
      exact (hcont.tendsto _).comp (hlim m)
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      simp only [Formalism.InvariantFactorPaths.G7.coeff_frobVar_of_not_dvd hp0 _ hi]
      exact tendsto_const_nhds
  exact le_of_tendsto hT.norm (Filter.Eventually.of_forall hk)
end Formalism.L2.Th1.D
