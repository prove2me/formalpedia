-- Prove2me | solution 1 for FamilyGenTest.ec_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:06:41.315705+00:00
-- url     : https://prove2.me/submissions/5d6a4795-b12b-44dd-a999-b42bb5b1178f

import Mathlib
import Definitions.Def_FamilyGenTest_Rewards

open FamilyGenTest in
theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (R : Rewards I) (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    (∑ γ, marginal μ s i γ * testedReward R i γ) - cost R μ s i - rbar R i (risk μ s i)
      = -rdelta R i * risk μ s i ^ 2 + (rdelta R i + censoring R i - R.cf i) * risk μ s i
        - R.cs i := by
  have hsum1 : ∑ γ, marginal μ s i γ = 1 := by
    unfold marginal
    rw [Finset.sum_fiberwise (compatible s) (fun g => g i) (FamilyGenTest.posterior μ s)]
    have : ∑ g ∈ compatible s, FamilyGenTest.posterior μ s g = ∑ g ∈ compatible s, μ.prob g / mass μ s :=
      Finset.sum_congr rfl (fun g hg => by unfold FamilyGenTest.posterior; rw [if_pos hg])
    rw [this, ← Finset.sum_div]
    exact div_self (ne_of_gt hs)
  have hsum : marginal μ s i 0 + marginal μ s i 1 + marginal μ s i 2 = 1 := by
    rwa [Fin.sum_univ_three] at hsum1
  have t0 : testedReward R i 0 = R.r0at0 i := by unfold testedReward; rw [if_pos rfl]
  have t1 : testedReward R i 1 = R.r1at1 i := by unfold testedReward; rw [if_neg (by decide)]
  have t2 : testedReward R i 2 = R.r1at1 i := by unfold testedReward; rw [if_neg (by decide)]
  rw [Fin.sum_univ_three, t0, t1, t2]
  unfold cost rbar rbar0 rbar1 rdelta censoring risk
  linear_combination R.r0at0 i * hsum
