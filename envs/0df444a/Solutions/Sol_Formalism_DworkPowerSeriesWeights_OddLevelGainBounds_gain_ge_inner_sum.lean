-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.gain_ge_inner_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:31.235802+00:00
-- url     : https://prove2.me/submissions/0acd393c-30cb-40d1-885c-8c8600500eb2

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementN
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_tsum_le_of_dominated
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_least_odd_top_level_spec

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
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution : GainDominatesInnerSum := by
  intro l d inst hl TT nu1 nu2 s
  classical
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb : Summable (fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) := by
    have : Summable (fun e : ℕ => ((l:ℝ)⁻¹) ^ e) :=
      summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
    simpa [div_eq_mul_inv, inv_pow] using this.mul_left (nu1 s : ℝ)
  unfold topTerm oddLevelGainSum
  refine tsum_le_of_dominated (b := fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) ?_ ?_ ?_ hb
  · intro e
    try dsimp only
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hn2 : (0:ℝ) ≤ (nu2 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hsub : ((nu1 s : ℝ) - nu2 s) / (l:ℝ) ^ e =
        (nu1 s : ℝ) / (l:ℝ) ^ e - (nu2 s : ℝ) / (l:ℝ) ^ e := sub_div _ _ _
    by_cases ho : Odd e
    swap
    · simp [ho]
    rcases lt_trichotomy (e : ℕ∞) (dTop d TT s) with hlt | heq | hgt
    · rw [if_pos (show Odd e ∧ (e : ℕ∞) < dTop d TT s from ⟨ho, hlt⟩)]
      split_ifs
      · apply max_le_max _ le_rfl
        rw [hsub]; linarith
      · exact le_max_right _ _
    · obtain ⟨⟨-, hmem⟩, hmin⟩ := least_odd_top_level_spec TT s e heq.symm
      have hP : ∃ s' ∈ TT, IsLeast {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) = s'} e :=
        ⟨s + (e : ZMod d), hmem, ⟨ho, rfl⟩, fun e' he' => hmin e' he'.1 (he'.2 ▸ hmem)⟩
      rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (lt_irrefl _ (heq ▸ h.2))),
        if_neg (show ¬ (Odd e ∧ dTop d TT s < (e : ℕ∞)) from fun h => (lt_irrefl _ (heq ▸ h.2)))]
      split_ifs with h
      · exact absurd hP h.2
      · exact le_rfl
    · rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (not_lt.mpr hgt.le h.2)),
        if_pos (show Odd e ∧ dTop d TT s < (e : ℕ∞) from ⟨ho, hgt⟩)]
      split_ifs
      · exact max_le (by rw [hsub]; linarith) hA'
      · exact hA'
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    split_ifs
    · exact max_le (by linarith) hA'
    · exact le_rfl
    · exact hA'
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
