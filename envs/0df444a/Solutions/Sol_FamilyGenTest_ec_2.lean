-- Prove2me | solution 1 for FamilyGenTest.ec_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:54:11.242222+00:00
-- url     : https://prove2.me/submissions/77f9e74f-9e6f-44be-8212-1e6c07339aec

import Mathlib
import Definitions.Def_FamilyGenTest_Pmax

namespace Aux_FGTec2

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

end Aux_FGTec2

open FamilyGenTest Aux_FGTec2 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (R : Rewards I) (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    ∑ γ, marginal μ s i γ * Vstar R μ (test s i γ)
      = Phi R μ s i * risk μ s i + Vstar R μ (test s i 0) := by
  have hsum := msum μ s hs i
  have hb0 := mnonneg μ s hs i 1
  have hc0 := mnonneg μ s hs i 2
  rw [Fin.sum_univ_three]
  unfold Phi risk alpha
  by_cases h : marginal μ s i 1 + marginal μ s i 2 = 0
  · have hb : marginal μ s i 1 = 0 := by linarith
    have hc : marginal μ s i 2 = 0 := by linarith
    rw [h, div_zero]
    linear_combination Vstar R μ (test s i 0) * hsum
      + (Vstar R μ (test s i 1) - Vstar R μ (test s i 0)) * hb
      + (Vstar R μ (test s i 2) - Vstar R μ (test s i 0)) * hc
  · have hk : marginal μ s i 1 / (marginal μ s i 1 + marginal μ s i 2)
        * (marginal μ s i 1 + marginal μ s i 2) = marginal μ s i 1 := div_mul_cancel₀ _ h
    linear_combination Vstar R μ (test s i 0) * hsum
      + (Vstar R μ (test s i 2) - Vstar R μ (test s i 1)) * hk
