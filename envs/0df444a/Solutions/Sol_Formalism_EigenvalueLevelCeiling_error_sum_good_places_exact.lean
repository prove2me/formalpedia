-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.error_sum_good_places_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:44:24.166018+00:00
-- url     : https://prove2.me/submissions/9d8d941f-ab80-4ceb-bb22-7d09bed20411

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_ErrSumGoodExact
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsComposeGeneral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverP
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverPSqTail
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_primeBoundsExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : ErrSumGoodExact := by
  intro PI hPI Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD
  obtain ⟨hB1, hB2, hB3⟩ := primeBoundsExact Y X2 hY hX2
  obtain ⟨hD1, hD2⟩ := hD
  have hQ : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime ∧ (p : ℝ) ≤ Y := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨hPI p hp.1, hp.2⟩
  have hQ' : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime := fun p hp => (hQ p hp).1
  have hR : ∀ p ∈ (PI.filter (fun p : ℕ => (p : ℝ) ≤ Y)).filter (fun p : ℕ => X2 < (p : ℝ)),
      p.Prime ∧ X2 < (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨(hQ p hp.1).1, hp.2⟩
  have e1 := hB1 _ hQ
  have e2 := hB2 _ hQ
  have e3 := hB3 _ hR
  have e4 := hD1 _ hQ'
  have e5 := hD2 _ hQ'
  rw [Finset.sum_filter] at e1 e2 e4 e5
  rw [Finset.sum_filter, Finset.sum_filter] at e3
  have hsum : ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p =
      2 * A1 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then Real.log (p : ℝ) / (p : ℝ) else 0) +
      2 * kw * (∑ p ∈ PI, if (p : ℝ) ≤ Y then th p * Real.log (p : ℝ) else 0) +
      2 * (T * ∑ p ∈ PI, if (p : ℝ) ≤ Y then add p * Real.log (p : ℝ) else 0) +
      2 * A2 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then
        (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) else 0) +
      2 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then Real.log (p : ℝ) else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold errGood
    split_ifs <;> ring
  rw [hsum]
  have h1 := mul_le_mul_of_nonneg_left e1 hA1
  have h2 := mul_le_mul_of_nonneg_left e4 hkw
  have h4 := mul_le_mul_of_nonneg_left e3 hA2
  have h4' : A2 * (2.04 / X2) = 2.04 * A2 / X2 := by ring
  linarith
end Formalism.EigenvalueLevelCeiling
