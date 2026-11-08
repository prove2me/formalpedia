-- Prove2me | solution 1 for FamilyGenTest.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:00:34.714682+00:00
-- url     : https://prove2.me/submissions/90f6e420-1a5a-42da-8de8-9efafad6f16a

import Mathlib
import Definitions.Def_FamilyGenTest_Rewards

namespace Aux_FGTeq12

open FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem mnonneg (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I) (γ : Fin 3) :
    0 ≤ marginal μ s i γ := by
  unfold marginal
  apply Finset.sum_nonneg
  intro g _
  unfold posterior
  split_ifs
  · exact div_nonneg (μ.nonneg g) (le_of_lt hs)
  · exact le_refl 0

theorem msum (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I) :
    marginal μ s i 0 + marginal μ s i 1 + marginal μ s i 2 = 1 := by
  have h := Finset.sum_fiberwise (compatible s) (fun g => g i) (posterior μ s)
  rw [Fin.sum_univ_three] at h
  unfold marginal
  rw [h]
  have hm : 0 < mass μ s := hs
  calc ∑ g ∈ compatible s, posterior μ s g
      = ∑ g ∈ compatible s, μ.prob g / mass μ s :=
        Finset.sum_congr rfl (fun g hg => by rw [posterior, if_pos hg])
    _ = (∑ g ∈ compatible s, μ.prob g) / mass μ s := (Finset.sum_div _ _ _).symm
    _ = 1 := div_self hm.ne'

end Aux_FGTeq12

open FamilyGenTest Aux_FGTeq12 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (R : Rewards I) (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    ∑ γ, marginal μ s i γ * testedReward R i γ
      = (1 - risk μ s i) * R.r0at0 i + risk μ s i * R.r1at1 i := by
  have hsum := msum μ s hs i
  have e0 : testedReward R i 0 = R.r0at0 i := by simp [testedReward]
  have e1 : testedReward R i 1 = R.r1at1 i := by simp [testedReward]
  have e2 : testedReward R i 2 = R.r1at1 i := by simp [testedReward]
  rw [Fin.sum_univ_three, e0, e1, e2]
  unfold risk
  linear_combination R.r0at0 i * hsum
