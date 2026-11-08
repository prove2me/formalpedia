-- Prove2me | solution 1 for GSCoord.appendix_II_step_B
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:24:29.965784+00:00
-- url     : https://prove2.me/submissions/1b9b4299-c7f3-42a3-91be-6ec0f440111f

import Mathlib
import Definitions.Def_GSCoord_Model

namespace Aux_GSCoord_B
open GSCoord

lemma joint_le (sys : SerialSystem) (N₁ : ℕ) (SB : ℤ) (hSB : 0 ≤ SB) :
    valJoint sys N₁ ≤ valFix sys N₁ SB := by
  unfold valFix
  refine le_iInf₂ fun S hS => ?_
  unfold valJoint
  exact iInf₂_le (S, SB) ⟨hS, hSB⟩

lemma SB_le (sys : SerialSystem) (N₁ : ℕ) (hN₁ : 1 ≤ N₁) (hN₁N : N₁ < sys.N) (SB : ℤ)
    (S : ℕ → ℤ) (hS : FeasibleFix sys N₁ SB S) :
    SB ≤ sys.sNplus1 + ∑ k ∈ Finset.Ico (N₁ + 1) (sys.N + 1), (sys.T k : ℤ) := by
  obtain ⟨_, hB, hE, hT, _, _⟩ := hS
  have key : ∀ j, N₁ + 1 ≤ j → j ≤ sys.N + 1 →
      S (N₁ + 1) ≤ S j + ∑ k ∈ Finset.Ico (N₁ + 1) j, (sys.T k : ℤ) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; simp
    | succ j hj ih =>
      intro hjN
      have h1 := ih (by omega)
      have h2 := hT j (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      rw [Finset.sum_Ico_succ_top hj]
      linarith
  have := key (sys.N + 1) (by omega) le_rfl
  rw [hB, hE] at this
  exact this

end Aux_GSCoord_B

open GSCoord Aux_GSCoord_B in
theorem solution (sys : SerialSystem) (N₁ : ℕ) (hN₁ : 1 ≤ N₁) (hN₁N : N₁ < sys.N) :
    IsLeast {v : EReal | ∃ SB : ℤ, 0 ≤ SB ∧ v = valFix sys N₁ SB} (valJoint sys N₁) := by
  refine ⟨?_, ?_⟩
  · set U := sys.sNplus1 + ∑ k ∈ Finset.Ico (N₁ + 1) (sys.N + 1), (sys.T k : ℤ) with hU
    set F := Finset.Icc (0 : ℤ) (max U 0) with hF
    have hFne : F.Nonempty := ⟨0, by simp [hF]⟩
    obtain ⟨SB0, hSB0, hmin⟩ := Finset.exists_min_image F (fun SB => valFix sys N₁ SB) hFne
    have hSB0' : 0 ≤ SB0 := (Finset.mem_Icc.1 hSB0).1
    refine ⟨SB0, hSB0', le_antisymm (joint_le sys N₁ SB0 hSB0') ?_⟩
    unfold valJoint
    refine le_iInf₂ fun p hp => ?_
    have hmem : p.2 ∈ F := by
      rw [hF, Finset.mem_Icc]
      exact ⟨hp.2, le_trans (SB_le sys N₁ hN₁ hN₁N p.2 p.1 hp.1) (le_max_left _ _)⟩
    calc valFix sys N₁ SB0 ≤ valFix sys N₁ p.2 := hmin _ hmem
      _ ≤ ((costP sys p.1 : ℝ) : EReal) := by
        unfold valFix
        exact iInf₂_le p.1 hp.1
  · rintro v ⟨SB, hSB, rfl⟩
    exact joint_le sys N₁ SB hSB
