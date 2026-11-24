-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.proposition_six
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:03.046673+00:00
-- url     : https://prove2.me/submissions/31528a6e-e6b8-4cb1-8c00-396051d0b1f5

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementN
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_gamma_nonneg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_inv_le_gamma
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_two_gamma_le_three_div
import Theorems.Thm_Formalism_IncomingBounds_incomingBound
import Theorems.Thm_Formalism_IncomingBounds_lemmaFa
import Theorems.Thm_Formalism_IncomingBounds_lemmaFc


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
theorem _root_.solution : PropSix7 := by
  intro l d inst hl hd hev TT k D w E hk hw hE hoff hon
  classical
  have hA := lemmaFa
  have hc := lemmaFc
  have hI := incomingBound
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hg := gamma_nonneg hl
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ s : ZMod d, w s := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ s ∈ TT, w s := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun s _ => (hw s).le)
  have hTS : T ≤ S := by
    rw [hS, hT]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => (hw s).le)
  obtain ⟨Ws, hWs⟩ : ∃ f : ZMod d → ℝ, f = fun s => ((k:ℝ) - 1) * w s := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ f : ZMod d → ℝ, f = fun s => if s ∈ TT then 2 * w s else 0 := ⟨_, rfl⟩
  have hWsapp : ∀ s, Ws s = ((k:ℝ) - 1) * w s := fun s => by rw [hWs]
  rw [← hS, ← hT, ← hWs]
  have hD0 : 0 ≤ D := fun s => by
    show (0:ℝ) ≤ D s
    have h1 := hw s
    have h2 := (hE s).1
    by_cases hs : s ∈ TT
    · rw [hon s hs]; nlinarith
    · rw [hoff s hs]; nlinarith
  have hE'0 : 0 ≤ E' := fun s => by
    show (0:ℝ) ≤ E' s
    rw [hE']
    try dsimp only
    split_ifs
    · linarith [hw s]
    · exact le_rfl
  have hDE : D + E' = Ws + E := by
    funext s
    simp only [Pi.add_apply, hE', hWs]
    by_cases hs : s ∈ TT
    · rw [if_pos hs, hon s hs]; ring
    · rw [if_neg hs, hoff s hs]; ring

  obtain ⟨⟨sD, hsD, -, hFsD⟩, -⟩ := hA l d hl hd hev D hD0
  have h2 := (hc l d hl hd hev D E' sD hD0 hE'0 ⟨hsD, hFsD⟩).2
  rw [hDE] at h2
  have hE'sum : ∑ s, E' s = 2 * T := by
    rw [hT, Finset.mul_sum, hE', ← Finset.sum_filter]
    simp
  rw [hE'sum] at h2

  have hWs0 : 0 ≤ Ws := fun s => by
    show (0:ℝ) ≤ Ws s
    rw [hWsapp]
    have := hw s
    have : (0:ℝ) ≤ (k:ℝ) - 1 := by linarith
    positivity
  obtain ⟨⟨sW, hsW, -, hFsW⟩, -⟩ := hA l d hl hd hev Ws hWs0
  have hoptW : IsOptDual l d Ws sW := ⟨hsW, hFsW⟩
  have h3 := (hc l d hl hd hev Ws E sW hWs0 (fun s => (hE s).1) hoptW).1
  have hinc := hI l d hl hd hev Ws sW hWs0 hoptW
  have hfilt : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s ≤ S / l := by
    have e1 : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), Ws s =
        ((k:ℝ) - 1) * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    have e2 : ∑ s, Ws s = ((k:ℝ) - 1) * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    rw [e1, e2, mul_div_assoc] at hinc
    have hk1 : 0 < (k:ℝ) - 1 := by linarith
    exact le_of_mul_le_mul_left hinc hk1
  have hgl := inv_le_gamma hl
  have hpt : ∀ s, E s * max (sW s - gam l) 0 ≤
      4 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0) := by
    intro s
    obtain ⟨hE0, hE4⟩ := hE s
    have hs0 := (hsW.1 s).1
    have hs1 := (hsW.1 s).2
    have hws := hw s
    have hm0 : 0 ≤ max (sW s - gam l) 0 := le_max_right _ _
    have hq : 0 ≤ 4 * w s / l := by positivity
    split_ifs with hcase
    · have hm : max (sW s - gam l) 0 ≤ 1 := max_le (by linarith) zero_le_one
      calc E s * max (sW s - gam l) 0 ≤ E s * 1 := mul_le_mul_of_nonneg_left hm hE0
        _ ≤ 4 * w s := by linarith
        _ ≤ _ := by linarith
    · push Not at hcase
      have h21 : 2 / (l:ℝ) = 1 / l + 1 / l := by ring
      have hm : max (sW s - gam l) 0 ≤ 1 / l := max_le (by linarith) (by positivity)
      calc E s * max (sW s - gam l) 0 ≤ (4 * w s) * (1 / l) :=
            mul_le_mul hE4 hm hm0 (by linarith)
        _ = 4 * w s / l + 4 * 0 := by ring
  have hsum3 : ∑ s, E s * max (sW s - gam l) 0 ≤ 8 / l * S := by
    calc ∑ s, E s * max (sW s - gam l) 0
        ≤ ∑ s, (4 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0)) :=
          Finset.sum_le_sum (fun s _ => hpt s)
      _ = 4 * S / l + 4 * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div,
            ← Finset.mul_sum, ← hS]
      _ ≤ 4 * S / l + 4 * (S / l) := by linarith
      _ = 8 / l * S := by ring
  constructor
  · have : gam l * (2 * T) = 2 * gam l * T := by ring
    linarith
  · have h2g := two_gamma_le_three_div hl
    have hT' : 2 * gam l * T ≤ 3 / l * S :=
      calc 2 * gam l * T ≤ 2 * gam l * S := mul_le_mul_of_nonneg_left hTS (by linarith)
        _ ≤ 3 / l * S := mul_le_mul_of_nonneg_right h2g hS0
    have h11 : 11 / (l:ℝ) * S = 3 / l * S + 8 / l * S := by ring
    linarith
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
