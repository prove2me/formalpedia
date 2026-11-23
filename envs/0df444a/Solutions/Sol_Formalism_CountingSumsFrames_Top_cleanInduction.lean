-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.cleanInduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:00.813835+00:00
-- url     : https://prove2.me/submissions/3f27426c-34f5-41a4-b085-4b4766353c62

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.CleanInduction := by
  intro M _ Deg FF FF' hFF hFF' τ level spare sym raw o c' Q hdeg hsym hraw hstep S hS
  classical
  have key : ∀ n : ℕ, ∀ x : τ, o + c' - level x ≤ n → o ≤ level x →
      (2 * (Q : ℤ) + 1) * ((o : ℤ) + c' - 1 - level x) ≤ (spare x).1 →
      ((o : ℤ) + c' - 1 - level x) ≤ (spare x).2 →
      ∃ g ∈ Deg, g - sym x ∈ FF (o + c') ∧ g ∈ FF' (o + c') := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn ho h1 h2
      by_cases hl : level x < o + c'
      · obtain ⟨ch, ρ, hρ, hρd, heq, hch⟩ := hstep x hl h1 h2
        have hy : ∀ y ∈ ch, ∃ g ∈ Deg, g - sym y ∈ FF (o + c') ∧ g ∈ FF' (o + c') := by
          intro y hy
          obtain ⟨hxy, hyo, hsp⟩ := hch y hy
          refine ih (o + c' - level y) (by omega) y le_rfl (by omega) ?_ ?_
          · simp only [hsp]
            push_cast at h1 ⊢
            linarith
          · simp only [hsp]
            push_cast at h2 ⊢
            linarith
        choose! gy hgyD hgyF hgyF' using hy
        refine ⟨raw x - ∑ y ∈ ch, gy y, Deg.sub_mem (hdeg x).2 (sum_mem fun y hy => hgyD y hy), ?_, ?_⟩
        · have hrw : raw x - ∑ y ∈ ch, gy y - sym x = ρ - ∑ y ∈ ch, (gy y - sym y) := by
            rw [Finset.sum_sub_distrib]
            calc raw x - ∑ y ∈ ch, gy y - sym x = (raw x - sym x) - ∑ y ∈ ch, gy y := by abel
              _ = (∑ y ∈ ch, sym y + ρ) - ∑ y ∈ ch, gy y := by rw [heq]
              _ = ρ - (∑ y ∈ ch, gy y - ∑ y ∈ ch, sym y) := by abel
          rw [hrw]
          exact (FF (o + c')).sub_mem hρ (sum_mem fun y hy => hgyF y hy)
        · exact (FF' (o + c')).sub_mem (hFF' (by omega : o + c' ≤ level x + c') (hraw x))
            (sum_mem fun y hy => hgyF' y hy)
      · refine ⟨0, Deg.zero_mem, ?_, (FF' (o + c')).zero_mem⟩
        rw [zero_sub]
        exact (FF (o + c')).neg_mem (hFF (by omega : o + c' ≤ level x) (hsym x))
  have hinit : ∀ x ∈ S, ∃ g ∈ Deg, g - sym x ∈ FF (o + c') ∧ g ∈ FF' (o + c') := by
    intro x hx
    obtain ⟨ho, hsp⟩ := hS x hx
    have hoz : (o : ℤ) ≤ level x := by exact_mod_cast ho
    refine key _ x le_rfl ho ?_ ?_
    · simp only [hsp]
      push_cast
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * Q + 1 by positivity) (show (0 : ℤ) ≤ level x - o by linarith),
        (show (0 : ℤ) ≤ Q by positivity), (show (0 : ℤ) ≤ c' by positivity)]
    · simp only [hsp]
      push_cast
      linarith
  choose! g hgD hgF hgF' using hinit
  refine ⟨∑ x ∈ S, g x, sum_mem fun x hx => hgD x hx, ?_, sum_mem fun x hx => hgF' x hx⟩
  rw [← Finset.sum_sub_distrib]
  exact sum_mem fun x hx => hgF x hx
end Formalism.CountingSumsFrames.Top
