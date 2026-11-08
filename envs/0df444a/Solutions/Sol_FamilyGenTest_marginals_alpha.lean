-- Prove2me | solution 1 for FamilyGenTest.marginals_alpha
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:25:20.661015+00:00
-- url     : https://prove2.me/submissions/b02e8ff7-9eb1-417d-b9ca-f86d6f36af4b

import Mathlib
import Definitions.Def_FamilyGenTest_risk

open FamilyGenTest in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    marginal μ s i 0 = 1 - risk μ s i ∧
    marginal μ s i 1 = alpha μ s i * risk μ s i ∧
    marginal μ s i 2 = (1 - alpha μ s i) * risk μ s i := by
  have hm : 0 < mass μ s := hs
  have hpost : ∑ g ∈ compatible s, FamilyGenTest.posterior μ s g = 1 := by
    rw [Finset.sum_congr rfl (fun g hg => (by rw [FamilyGenTest.posterior, if_pos hg] :
      FamilyGenTest.posterior μ s g = μ.prob g / mass μ s)), ← Finset.sum_div]
    exact div_self hm.ne'
  have h3 : marginal μ s i 0 + marginal μ s i 1 + marginal μ s i 2 = 1 := by
    rw [← hpost, ← Finset.sum_fiberwise (compatible s) (fun g => g i) (FamilyGenTest.posterior μ s),
      Fin.sum_univ_three]
    rfl
  have hnn : ∀ γ, 0 ≤ marginal μ s i γ := by
    intro γ
    refine Finset.sum_nonneg (fun g _ => ?_)
    unfold FamilyGenTest.posterior
    split_ifs
    · exact div_nonneg (μ.nonneg g) hm.le
    · exact le_refl 0
  have h1 := hnn 1
  have h2 := hnn 2
  refine ⟨by unfold risk; linarith, ?_, ?_⟩
  · unfold alpha risk
    by_cases h0 : marginal μ s i 1 + marginal μ s i 2 = 0
    · rw [h0, mul_zero]; linarith
    · rw [div_mul_cancel₀ _ h0]
  · unfold alpha risk
    by_cases h0 : marginal μ s i 1 + marginal μ s i 2 = 0
    · rw [h0, mul_zero]; linarith
    · rw [sub_mul, one_mul, div_mul_cancel₀ _ h0]; ring
