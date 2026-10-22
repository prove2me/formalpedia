-- Prove2me | solution 1 for BatteryLease.WinWin.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:45:53.337217+00:00
-- url     : https://prove2.me/submissions/8d58dfe6-1854-436e-8dd6-994158654ed9

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

set_option autoImplicit false
open MeasureTheory BatteryLease.WinWin

theorem solution (a ρ rh ch τ ph pbh pbl : ℝ) (hS : Standing a ρ rh ch)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (pbh < 0 → upVol a rh τ pbh = τ) ∧
    (0 ≤ pbh → pbh ≤ rh → upVol a rh τ pbh = τ * (a - pbh) / a) ∧
    (rh < pbh → upVol a rh τ pbh = 0) ∧
    (a < pbh → upVol a rh τ pbh = 0) ∧
    (pbl < ph - rh → downVol a rh τ ph pbl = 1 - τ) ∧
    (ph - rh ≤ pbl → pbl ≤ ph → downVol a rh τ ph pbl = (1 - τ) * (ph - pbl) / a) ∧
    (pbl < ph - a → downVol a rh τ ph pbl = 1 - τ) ∧
    (ph < pbl → downVol a rh τ ph pbl = 0) := by
  obtain ⟨ha1, -, ⟨hrh0, hrha⟩, -⟩ := hS
  have ha0 : 0 < a := by linarith
  have hane : a ≠ 0 := ne_of_gt ha0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hset : {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ pos (D - rh) + pbh ≤ D} = Set.Icc 0 a := by
      ext D
      simp only [Set.mem_setOf_eq, pos]
      constructor
      · exact fun h => h.1
      · intro hD
        refine ⟨hD, ?_⟩
        rcases le_total (D - rh) 0 with h1 | h1
        · rw [max_eq_right h1]; linarith [hD.1]
        · rw [max_eq_left h1]; linarith
    unfold upVol
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    field_simp; ring
  · intro h0 h1
    have hset : {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ pos (D - rh) + pbh ≤ D} = Set.Icc pbh a := by
      ext D
      simp only [Set.mem_setOf_eq, pos, Set.mem_Icc]
      constructor
      · rintro ⟨⟨hD0, hDa⟩, h⟩
        refine ⟨?_, hDa⟩
        have := le_max_right (D - rh) 0
        linarith
      · rintro ⟨hD0, hDa⟩
        refine ⟨⟨by linarith, hDa⟩, ?_⟩
        rcases le_total (D - rh) 0 with h1 | h1
        · rw [max_eq_right h1]; linarith
        · rw [max_eq_left h1]; linarith
    unfold upVol
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  · intro h
    have hset : {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ pos (D - rh) + pbh ≤ D} = ∅ := by
      ext D
      simp only [Set.mem_setOf_eq, pos, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hD
      have := le_max_left (D - rh) 0
      linarith
    unfold upVol
    rw [hset]; simp
  · intro h
    have hset : {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ pos (D - rh) + pbh ≤ D} = ∅ := by
      ext D
      simp only [Set.mem_setOf_eq, pos, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hD
      have := le_max_right (D - rh) 0
      linarith [hD.2]
    unfold upVol
    rw [hset]; simp
  · intro h
    have hset : {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ D + pbl < pos (D - rh) + ph} = Set.Icc 0 a := by
      ext D
      simp only [Set.mem_setOf_eq, pos]
      constructor
      · exact fun h => h.1
      · intro hD
        refine ⟨hD, ?_⟩
        have := le_max_left (D - rh) 0
        linarith
    unfold downVol
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    field_simp; ring
  · intro h1 h2
    have hset : {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ D + pbl < pos (D - rh) + ph} =
        Set.Ico 0 (ph - pbl) := by
      ext D
      simp only [Set.mem_setOf_eq, pos, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨⟨hD0, hDa⟩, h⟩
        refine ⟨hD0, ?_⟩
        rcases le_total (D - rh) 0 with h3 | h3
        · rw [max_eq_right h3] at h; linarith
        · rw [max_eq_left h3] at h; linarith
      · rintro ⟨hD0, hD1⟩
        refine ⟨⟨hD0, by linarith⟩, ?_⟩
        have := le_max_right (D - rh) 0
        linarith
    unfold downVol
    rw [hset, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
    ring
  · intro h
    have hset : {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ D + pbl < pos (D - rh) + ph} = Set.Icc 0 a := by
      ext D
      simp only [Set.mem_setOf_eq, pos]
      constructor
      · exact fun h => h.1
      · intro hD
        refine ⟨hD, ?_⟩
        have := le_max_right (D - rh) 0
        linarith [hD.2]
    unfold downVol
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    field_simp; ring
  · intro h
    have hset : {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ D + pbl < pos (D - rh) + ph} = ∅ := by
      ext D
      simp only [Set.mem_setOf_eq, pos, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hD
      rcases le_total (D - rh) 0 with h3 | h3
      · rw [max_eq_right h3]; linarith [hD.1]
      · rw [max_eq_left h3]; linarith
    unfold downVol
    rw [hset]; simp
