-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.inv_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:50.260091+00:00
-- url     : https://prove2.me/submissions/ef20d7b3-fab4-4db8-9cbe-70dfbba43185

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_cnt_succ
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_PRun_zero
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_PRun_ext

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
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution {n : ℕ} (hn : Even n) {T : Finset ℕ} {L₂ R b K₀ : ℕ} (hR : 1 ≤ R) (t : ℕ) (s : St)
    (hs : Inv n T L₂ R b K₀ t s) :
    Inv n T L₂ R b K₀ (t + 1) (step R L₂ s (decide ((b + (t + 1)) % n ∈ T))) := by
  cases s with
  | bad =>
    have : step R L₂ .bad (decide ((b + (t + 1)) % n ∈ T)) = .bad := by
      cases decide ((b + (t + 1)) % n ∈ T) <;> rfl
    rw [this]; exact True.intro
  | good =>
    have : step R L₂ .good (decide ((b + (t + 1)) % n ∈ T)) = .good := by
      cases decide ((b + (t + 1)) % n ∈ T) <;> rfl
    rw [this]
    obtain ⟨u, h1, h2, h3, h4, h5⟩ := hs
    exact ⟨u, h1, fun l => (h2 l).trans (Nat.le_succ _), h3, h4, h5⟩
  | run K j d al ev =>
    obtain ⟨hK1, hK2, hj, hd, hev, htop, hnone, hcnt, hal⟩ := hs
    have hev' : (!ev) = decide (Even (b + (t + 1))) := by
      rw [hev, ← add_assoc]
      by_cases he : Even (b + t)
      · simp [he, Nat.even_add_one]
      · simp [he, Nat.even_add_one]
    by_cases hT : (b + (t + 1)) % n ∈ T
    · rw [decide_eq_true hT]
      have hext : (al && okG L₂ j d ev) = true →
          ∃ u : Fin (j + 1) → ℕ, PRun n T L₂ b (j + 1) (t + 1) 0 u := by
        intro hg
        rw [Bool.and_eq_true] at hg
        obtain ⟨u, hu⟩ := hal hg.1
        exact ⟨_, PRun_ext hn hu hd hev hnone hT hg.2⟩
      have hc1 : cnt n T b (t + 1) = cnt n T b t + 1 := by rw [cnt_succ, if_pos hT]
      simp only [step]
      split_ifs with hjR hg hK
      · obtain ⟨u, hu⟩ := hext hg
        subst hjR
        exact ⟨u, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1⟩
      · exact True.intro
      · refine ⟨by omega, by omega, by omega, by omega, hev', by simpa using hT,
          fun x h1 h2 => by omega, ?_, fun _ => ⟨Fin.elim0, PRun_zero _ _ _ _ _ _ _⟩⟩
        rw [hc1, hcnt]
        have e : K₀ - (K - 1) = (K₀ - K) + 1 := by omega
        rw [e, mul_add, mul_one]
        omega
      · refine ⟨hK1, hK2, by omega, by omega, hev', by simpa using hT,
          fun x h1 h2 => by omega, ?_, hext⟩
        rw [hc1, hcnt]
        omega
    · rw [decide_eq_false hT]
      simp only [step]
      refine ⟨hK1, hK2, hj, by omega, hev', ?_, ?_, ?_, ?_⟩
      · rwa [show t + 1 - (d + 1) = t - d by omega]
      · intro x h1 h2
        rcases Nat.lt_or_ge x (t + 1) with h | h
        · exact hnone x (by omega) (by omega)
        · have : x = t + 1 := by omega
          subst this; exact hT
      · rw [cnt_succ, if_neg hT, hcnt, add_zero]
      · intro ha
        obtain ⟨u, hmono, hle, htopu, hevu, hgap, hlast⟩ := hal ha
        refine ⟨u, hmono, fun l => (hle l).trans (Nat.le_succ _), htopu, hevu, hgap, ?_⟩
        intro h
        rw [hlast h]
        omega
end Formalism.G0.TopsWeightFunctionBounds
