-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.no_residue_displaced_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:07.733131+00:00
-- url     : https://prove2.me/submissions/80681f21-a3b7-41e8-befa-ee767dacdd3c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_slack_size_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLargePrime_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsThin_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsTop_holds
import Theorems.Thm_Formalism_CohomologicalDescent_windowResidueCountEqZero_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution : NoResDisplaced := by
  intro P H G l hlp hl U bot c e δ σ hδ hS hk
  obtain ⟨hσ, hc, hU⟩ := hS
  have N := LogSmallConstantBounds.natBounds H
  have d := LogSmallConstantBounds.paramsLargePrime_holds P H G l hl
  have fE := LogSmallConstantBounds.paramsTop_holds P H G
  have fF := LogSmallConstantBounds.paramsThin_holds P H G
  have sl := slack_size_holds P H G
  have r2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := by ring
  have r8 : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  have t6 := N.t6
  have hr48 : 48 * (P.t : ℝ) ^ 2 ≤ P.b / P.lstar := sl.1
  have hr3 : (3 : ℝ) ≤ P.b / P.lstar := by nlinarith
  have hκ0 := sl.2 l hl

  have hκ : (P.kap l : ℝ) + |δ| ≤ 2 * (P.b / P.lstar) - 1 := by linarith
  have hκm : (P.kap l : ℝ) + |δ| ≤ (P.kmax : ℝ) := by
    have : 2 * P.b / P.lstar < (P.kmax : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [r2] at this
    linarith
  have hδ' := abs_le.mp (le_refl |δ|)
  apply windowResidueCountEqZero_holds
  intro u hu hub x hx
  rw [Finset.mem_Icc] at hx
  have x1 : (bot : ℝ) - (P.kap l : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx.1
  have x2 : (x : ℝ) ≤ (bot : ℝ) + (P.t : ℝ) - 1 + (P.kap l : ℝ) := by exact_mod_cast hx.2
  have hs2 : (σ : ℝ) = 1 ∨ (σ : ℝ) = -1 := by rcases hσ with h | h <;> simp [h]
  have hcast : ((|u - x| : ℤ) : ℝ) = |(u : ℝ) - (x : ℝ)| := by push_cast; rfl
  have hzc : ((σ * (u - x) : ℤ) : ℝ) =
      ((σ : ℝ) * ((u : ℝ) - c) + e) - ((σ : ℝ) * ((x : ℝ) - c) + e) := by push_cast; ring
  have hB : |(σ : ℝ) * ((x : ℝ) - c) + e| ≤ ((P.t : ℝ) - 1) / 2 + ((P.kap l : ℝ) + |δ|) := by
    have e1 : (σ : ℝ) * ((x : ℝ) - c) + e =
        (σ : ℝ) * ((x : ℝ) - (bot : ℝ) - ((P.t : ℝ) - 1) / 2) + δ := by
      linear_combination hc
    have e2 : |(σ : ℝ) * ((x : ℝ) - (bot : ℝ) - ((P.t : ℝ) - 1) / 2)| ≤
        ((P.t : ℝ) - 1) / 2 + (P.kap l : ℝ) := by
      rw [abs_mul]
      have : |(σ : ℝ)| = 1 := by rcases hs2 with h | h <;> simp [h]
      rw [this, one_mul, abs_le]; constructor <;> linarith
    rw [e1]
    have := abs_add_le ((σ : ℝ) * ((x : ℝ) - (bot : ℝ) - ((P.t : ℝ) - 1) / 2)) δ
    linarith
  have hAB : |((σ : ℝ) * ((u : ℝ) - c) + e) - ((σ : ℝ) * ((x : ℝ) - c) + e)| = |(u : ℝ) - (x : ℝ)| := by
    have : ((σ : ℝ) * ((u : ℝ) - c) + e) - ((σ : ℝ) * ((x : ℝ) - c) + e)
        = (σ : ℝ) * ((u : ℝ) - (x : ℝ)) := by ring
    rw [this, abs_mul]
    have : |(σ : ℝ)| = 1 := by rcases hs2 with h | h <;> simp [h]
    rw [this, one_mul]
  generalize hAdef : (σ : ℝ) * ((u : ℝ) - c) + e = A at *
  generalize hBdef : (σ : ℝ) * ((x : ℝ) - c) + e = B at *
  have hBB := abs_le.mp hB
  have crit : 0 < |A - B| → |A - B| < (l : ℝ) → (0 < |u - x| ∧ |u - x| < (l : ℤ)) := by
    intro a1 a2
    rw [hAB, ← hcast] at a1 a2
    exact ⟨by exact_mod_cast a1, by exact_mod_cast a2⟩
  rcases hU u hu hub with hcl | hlow
  ·
    have hv : (σ : ℝ) * ((u : ℝ) - c) = A - e := by linarith
    rw [hv] at hcl
    rcases hk with ⟨hth, hex⟩ | htop | hthin
    · right
      intro hdvd
      apply hex
      refine ⟨σ * (u - x), ?_, ?_, Dvd.dvd.mul_left hdvd σ⟩
      · rw [hzc]; have := hth.1; linarith [hBB.2]
      · rw [hzc]; have := hth.2; linarith [hBB.1]
    · left
      obtain ⟨bt, b1, b2, b3, b4⟩ := htop
      have bp := H.b'_pos
      have hx := H.x_ge
      have q1 : 0 ≤ P.b' / P.x := by positivity
      have tl := G.top_le
      have e1 : P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) = P.b' * (1 + 1 / P.x ^ 2) + P.b' / P.x := by ring
      rw [e1] at tl
      have pos : 0 < A - B := by linarith [hBB.2, fF.1, fF.2]
      apply crit
      · rw [abs_of_pos pos]; exact pos
      · rw [abs_of_pos pos]; linarith [hBB.1, fF.1, fF.2]
    · left
      have bp := H.b'_pos
      have hx := H.x_ge
      have q1 : 0 ≤ P.b' / P.x := by positivity
      have q2 : 0 ≤ P.b' * (1 / P.x ^ 2) := by positivity
      have tl := G.top_le
      have e1 : P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) = P.b' + P.b' * (1 / P.x ^ 2) + P.b' / P.x := by ring
      rw [e1] at tl
      have pos : 0 < A - B := by linarith [hBB.2, fF.1, fF.2, hthin.1]
      apply crit
      · rw [abs_of_pos pos]; exact pos
      · rw [abs_of_pos pos]; linarith [hBB.1, fF.1, fF.2, hthin.2]
  ·
    left
    rw [r2, hAdef] at hlow
    have g1 : |A| - |B| ≤ |A - B| := abs_sub_abs_le_abs_sub A B
    have g2 : |A - B| ≤ |A| + |B| := abs_sub A B
    have w := H.win_lt
    rw [r8] at w
    have te := H.t_le
    have dl := d.1
    apply crit
    · linarith [hlow.1]
    · linarith [hlow.2]
end Formalism.CohomologicalDescent.WorkedExample
