-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.CosetIndexLemmas.rounding_rd_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:43:55.902814+00:00
-- url     : https://prove2.me/submissions/f815772c-668d-4dc7-ab8d-f7f413f50abe

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_theta_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.CosetIndexLemmas
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost
open Formalism.LFunctionChainParameters.DeficitSplitLemmas
namespace Formalism.LFunctionChainParameters.CosetIndexLemmas
theorem _root_.solution : RoundingRd := by
  classical
  intro ι W pr l sg sg' R X'' g₁ g₂ T hl hunit h1 h0 hR hX hg1 hg2 hT

  have s1 : ∑ w ∈ W, 2 * l w * (sg w - sg' w) ≤ ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w := by
    rw [← Finset.sum_filter_add_sum_filter_not W (fun w => pr w ∈ R)]
    have hA : ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w * (sg w - sg' w)
        ≤ ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w := by
      refine Finset.sum_le_sum fun w hw => ?_
      have hw' := (Finset.mem_filter.1 hw).1
      nlinarith [hl w hw', h1 w hw']
    have hB : ∑ w ∈ W.filter (fun w => ¬ pr w ∈ R), 2 * l w * (sg w - sg' w) ≤ 0 := by
      refine Finset.sum_nonpos fun w hw => ?_
      have hw' := Finset.mem_filter.1 hw
      nlinarith [hl w hw'.1, h0 w hw'.1 hw'.2]
    linarith

  have s2 : ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w = ∑ p ∈ R, 2 * Real.log p := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := W.filter (fun w => pr w ∈ R)) (t := R) (g := pr)
      (fun w hw => (Finset.mem_filter.1 hw).2)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hunit p hp, Finset.mul_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, _⟩, he⟩; exact ⟨hw, he⟩
    · rintro ⟨hw, he⟩; exact ⟨⟨hw, he ▸ hp⟩, he⟩

  have s3 : ∑ p ∈ R, 2 * Real.log p ≤ (2 * Real.log 4 + 6) * X'' := by
    rw [← Finset.sum_filter_add_sum_filter_not R (fun p : ℕ => (p : ℝ) ≤ X'')]
    have hA : ∑ p ∈ R.filter (fun p : ℕ => (p : ℝ) ≤ X''), 2 * Real.log p ≤ 2 * (Real.log 4 * X'') := by
      rw [← Finset.mul_sum]
      have := theta_finite X'' (R.filter (fun p : ℕ => (p : ℝ) ≤ X'')) hX (fun p hp =>
        ⟨(hR p (Finset.mem_filter.1 hp).1).1, (Finset.mem_filter.1 hp).2⟩)
      linarith
    have hnn : ∀ j : ℕ, 0 ≤ Real.log (j : ℝ) := fun j => Real.log_natCast_nonneg j
    have hB : ∑ p ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X''), 2 * Real.log p
        ≤ 2 * Real.log g₁ + 2 * Real.log g₂ + 2 * Real.log T := by
      have hle : ∀ p ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X''), 2 * Real.log (p : ℝ)
          ≤ (if p = g₁ then 2 * Real.log (g₁ : ℝ) else 0) + (if p = g₂ then 2 * Real.log (g₂ : ℝ) else 0)
            + (if p = T then 2 * Real.log (T : ℝ) else 0) := by
        intro p hp
        have hp' := Finset.mem_filter.1 hp
        have nn : ∀ (P : Prop) [Decidable P] (c : ℝ), 0 ≤ c → 0 ≤ (if P then c else 0) := by
          intro P _ c hc; split_ifs <;> [exact hc; exact le_refl _]
        have n1 := nn (p = g₁) (2 * Real.log (g₁ : ℝ)) (by linarith [hnn g₁])
        have n2 := nn (p = g₂) (2 * Real.log (g₂ : ℝ)) (by linarith [hnn g₂])
        have n3 := nn (p = T) (2 * Real.log (T : ℝ)) (by linarith [hnn T])
        rcases (hR p hp'.1).2 with h | h | h | h
        · exact absurd h hp'.2
        · have e : (if p = g₁ then 2 * Real.log (g₁ : ℝ) else 0) = 2 * Real.log (p : ℝ) := by rw [if_pos h, h]
          linarith
        · have e : (if p = g₂ then 2 * Real.log (g₂ : ℝ) else 0) = 2 * Real.log (p : ℝ) := by rw [if_pos h, h]
          linarith
        · have e : (if p = T then 2 * Real.log (T : ℝ) else 0) = 2 * Real.log (p : ℝ) := by rw [if_pos h, h]
          linarith
      refine (Finset.sum_le_sum hle).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
      have m1 : ∀ (c : ℝ) (P : Prop) [Decidable P], 0 ≤ c → (if P then c else 0) ≤ c := by
        intro c P _ hc; split_ifs <;> [exact le_refl _; exact hc]
      have := m1 (2 * Real.log (g₁ : ℝ)) (g₁ ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X'')) (by linarith [hnn g₁])
      have := m1 (2 * Real.log (g₂ : ℝ)) (g₂ ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X'')) (by linarith [hnn g₂])
      have := m1 (2 * Real.log (T : ℝ)) (T ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X'')) (by linarith [hnn T])
      linarith
    linarith
  linarith
end Formalism.LFunctionChainParameters.CosetIndexLemmas
