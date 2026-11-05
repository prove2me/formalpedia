-- Prove2me | solution 1 for ExploreFirst.Asymptotic.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:59:36.813049+00:00
-- url     : https://prove2.me/submissions/7b7b6b5f-198f-4062-8200-e5ef67452213

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting
import Theorems.Thm_ExploreFirst_Asymptotic_one_alternative

open ExploreFirst.Asymptotic

theorem solution {K : ℕ} (𝒟 : Set (MeasureTheory.Measure ℝ))
    (h𝒟 : IsModel 𝒟) (π : BanditAlgorithm.BanditPolicy K)
    (hπ : IsUniformlyFastConvergent 𝒟 π)
    (ν : BanditAlgorithm.StochasticBandit K) (hν : InModel 𝒟 ν)
    (a : Fin K) (hsub : 0 < BanditAlgorithm.banditGap ν a) :
    (BanditAlgorithm.banditDInf 𝒟 (ν.P a) (BanditAlgorithm.banditOptimalMean ν))⁻¹ ≤
      Filter.liminf (fun T : ℕ =>
        ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a / Real.log T)) Filter.atTop := by
  unfold BanditAlgorithm.banditDInf
  rw [ENNReal.inv_iInf]
  refine iSup_le fun Q => ?_
  rw [ENNReal.inv_iInf]
  refine iSup_le fun hQ => ?_
  obtain ⟨hQ𝒟, hQμ⟩ := hQ
  haveI hQp : MeasureTheory.IsProbabilityMeasure Q := (h𝒟 Q hQ𝒟).1
  let ν' : BanditAlgorithm.StochasticBandit K :=
    { P := Function.update ν.P a Q
      prob := by
        intro i
        by_cases hi : i = a
        · subst hi; simpa using hQp
        · rw [Function.update_of_ne hi]; exact ν.prob i }
  have hP : ν'.P a = Q := by simp [ν']
  have h := one_alternative 𝒟 h𝒟 π hπ ν ν' hν a hsub
    (fun k hk => by simp [ν', Function.update_of_ne hk]) (by rw [hP]; exact hQ𝒟)
    (by unfold BanditAlgorithm.banditArmMean; rw [hP]; exact hQμ)
  rw [hP] at h
  exact h
