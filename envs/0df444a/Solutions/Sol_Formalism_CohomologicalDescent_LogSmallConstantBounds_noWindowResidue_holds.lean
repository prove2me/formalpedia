-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.noWindowResidue_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:37.813517+00:00
-- url     : https://prove2.me/submissions/2ab14ae9-2abf-4579-b0fb-9d862e136ea6

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_div_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_mul_lstar_le_b
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_eta_nonneg__1aa77f39dc77
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_kmax_le
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLargePrime_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsTop_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsThin_holds
import Theorems.Thm_Formalism_CohomologicalDescent_windowResidueCountEqZero_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
private theorem size_bounds_of_large {P : Par} (H : P.Hyp) (G : P.Large) :
    P.S + P.η < P.lstar ∧ 2 * P.η + P.t + 8 * (P.b / P.lstar) + 7 < P.lstar ∧
      2 * P.lstar ≤ P.b ∧ 0 < P.b / P.lstar ∧ (P.kmax : ℝ) ≤ 2 * (P.b / P.lstar) ∧
      P.h = P.b + P.S + P.η + P.t + 1 ∧ 0 ≤ P.η ∧ (P.t : ℝ) ≤ P.η ∧ 0 ≤ P.S ∧ 0 < P.lstar := by
  have h1 := H.sum_lt
  have h2 := H.win_lt
  have hb' := H.b'_pos
  have hbl := b_div_lstar_pos H G
  have e : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  exact ⟨by linarith, by linarith, two_mul_lstar_le_b H G, hbl, kmax_le H G, rfl, eta_nonneg' H,
    H.t_le, H.S_nonneg, lstar_pos H G⟩
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : NoResidueInWindow := by
  intro P H G l hl hlJ U bot c e σ hS hK
  have nb := natBounds H
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := size_bounds_of_large H G
  obtain ⟨hlst, hkap2, hkapmax, htk, hetk, hNr, hSk, hhN⟩ := paramsLargePrime_holds P H G l hlJ
  have hT := paramsTop_holds P H G
  obtain ⟨hth1, hth2⟩ := paramsThin_holds P H G
  have hw := G.w_gt
  have htop := G.top_le
  have hx := H.x_ge
  have hb' := H.b'_pos
  have e2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := by ring
  have hkapR : (P.kap l : ℝ) ≤ P.kmax := by exact_mod_cast hkapmax
  have hxinv : 0 ≤ P.b' / P.x := div_nonneg hb'.le (by linarith)
  have hxinv2 : 0 ≤ P.b' / P.x ^ 2 := div_nonneg hb'.le (by positivity)
  have htopE : P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) = P.b' + P.b' / P.x + P.b' / P.x ^ 2 := by ring
  have htopE2 : P.b' * (1 + 1 / P.x ^ 2) = P.b' + P.b' / P.x ^ 2 := by ring
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  obtain ⟨hσ, hc, hU⟩ := hS
  have hσabs : |(σ : ℝ)| = 1 := by rcases hσ with h | h <;> simp [h]
  refine Formalism.CohomologicalDescent.windowResidueCountEqZero_holds l bot P.t (P.kap l) U ?_
  intro u hu hun x hx'
  rw [Finset.mem_Icc] at hx'
  have hx1 : (bot : ℝ) - P.kap l ≤ x := by exact_mod_cast hx'.1
  have hx2 : (x : ℝ) ≤ bot + P.t - 1 + P.kap l := by exact_mod_cast hx'.2
  have hdabs : |(σ : ℝ) * ((x : ℝ) - (bot + ((P.t : ℝ) - 1) / 2))| ≤ ((P.t : ℝ) - 1) / 2 + P.kap l := by
    rw [abs_mul, hσabs, one_mul, abs_le]
    constructor <;> linarith
  have hd := abs_le.1 hdabs
  have hyx : (σ : ℝ) * ((u : ℝ) - x) = (σ : ℝ) * ((u : ℝ) - c) + e
      - (σ : ℝ) * ((x : ℝ) - (bot + ((P.t : ℝ) - 1) / 2)) := by
    linear_combination (-1 : ℝ) * hc
  have habs : |((u - x : ℤ) : ℝ)| = |(σ : ℝ) * ((u : ℝ) - x)| := by
    rw [abs_mul, hσabs, one_mul, Int.cast_sub]
  have fin : 0 < |(σ : ℝ) * ((u : ℝ) - x)| → |(σ : ℝ) * ((u : ℝ) - x)| < l →
      (0 < |u - x| ∧ |u - x| < (l : ℤ)) := by
    intro h1 h2
    rw [← habs] at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  rcases hU u hu hun with ⟨hv0, hvS⟩ | ⟨hA1, hA2⟩
  · rcases hK with ⟨⟨hTh1, hTh2⟩, hEx⟩ | ⟨bt, hbt1, hbt2, hbt3, hbt4⟩ | ⟨hTn1, hTn2⟩
    · right
      intro hdvd
      apply hEx
      refine ⟨σ * (u - x), ?_, ?_, Dvd.dvd.mul_left hdvd σ⟩
      · push_cast
        linarith
      · push_cast
        linarith
    · left
      have ylo : 0 < (σ : ℝ) * ((u : ℝ) - x) := by rw [hyx]; linarith
      have yhi : (σ : ℝ) * ((u : ℝ) - x) < l := by rw [hyx]; linarith
      exact fin (by rw [abs_of_pos ylo]; exact ylo) (by rw [abs_of_pos ylo]; exact yhi)
    · left
      have ylo : 0 < (σ : ℝ) * ((u : ℝ) - x) := by rw [hyx]; linarith
      have yhi : (σ : ℝ) * ((u : ℝ) - x) < l := by rw [hyx]; linarith
      exact fin (by rw [abs_of_pos ylo]; exact ylo) (by rw [abs_of_pos ylo]; exact yhi)
  · left
    have hy : (σ : ℝ) * ((u : ℝ) - x) = ((σ : ℝ) * ((u : ℝ) - c) + e)
        - (σ : ℝ) * ((x : ℝ) - (bot + ((P.t : ℝ) - 1) / 2)) := by rw [hyx]
    have h1 := abs_sub_abs_le_abs_sub ((σ : ℝ) * ((u : ℝ) - c) + e)
      ((σ : ℝ) * ((x : ℝ) - (bot + ((P.t : ℝ) - 1) / 2)))
    rw [← hy] at h1
    have hA2' := abs_le.1 hA2
    exact fin (by linarith) (abs_lt.2 ⟨by linarith, by linarith⟩)
end Formalism.CohomologicalDescent.LogSmallConstantBounds
