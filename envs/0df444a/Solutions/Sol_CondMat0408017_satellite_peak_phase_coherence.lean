-- Prove2me | solution 1 for CondMat0408017.satellite_peak_phase_coherence
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:32:02.47873+00:00
-- url     : https://prove2.me/submissions/f6eead91-9695-4c2f-91eb-cdf3b45aa6ed

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (eps0 ω c θ0 θs qn qm : ℝ) (heps0 : 0 < eps0)
    (hω : 0 < ω) (hc : 0 < c) :
    (∀ rB rC : ℝ × ℝ, doublePathPhaseDiff eps0 ω c θ0 θs qn qm rB rC =
      dot2 (rC - rB) (incWaveVec eps0 ω c θ0 + scatWaveVec eps0 ω c θs) +
        eucl (rC - rB) * (qn - qm)) ∧
    (∀ xB xC : ℝ, xB < xC →
      (doublePathPhaseDiff eps0 ω c θ0 θs qn qm (xB, 0) (xC, 0) = 0 ↔
        Real.sin θs = -Real.sin θ0 - 1 / Real.sqrt eps0 * (c / ω) * (qn - qm))) ∧
    ((∃ xB xC : ℝ, xB ≠ xC ∧ doublePathPhaseDiff eps0 ω c θ0 θs qn qm (xB, 0) (xC, 0) = 0) ↔
      (Real.sin θs = -Real.sin θ0 + 1 / Real.sqrt eps0 * (c / ω) * |qn - qm| ∨
        Real.sin θs = -Real.sin θ0 - 1 / Real.sqrt eps0 * (c / ω) * |qn - qm|)) := by
  have hpart1 : ∀ rB rC : ℝ × ℝ, doublePathPhaseDiff eps0 ω c θ0 θs qn qm rB rC =
      dot2 (rC - rB) (incWaveVec eps0 ω c θ0 + scatWaveVec eps0 ω c θs) +
        eucl (rC - rB) * (qn - qm) := by
    intro rB rC
    simp only [doublePathPhaseDiff, pathPhase, dot2, eucl, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_add, Prod.snd_add]
    have heucl : Real.sqrt ((rB.1 - rC.1) ^ 2 + (rB.2 - rC.2) ^ 2) =
        Real.sqrt ((rC.1 - rB.1) ^ 2 + (rC.2 - rB.2) ^ 2) := by
      congr 1; ring
    rw [heucl]
    ring
  have hsq : 0 < Real.sqrt eps0 := Real.sqrt_pos.mpr heps0
  have hwc : 0 < ω / c := div_pos hω hc
  have hfac : 0 < Real.sqrt eps0 * (ω / c) := mul_pos hsq hwc
  have heval : ∀ xB xC : ℝ, doublePathPhaseDiff eps0 ω c θ0 θs qn qm (xB, 0) (xC, 0) =
      (xC - xB) * (Real.sqrt eps0 * (ω / c) * (Real.sin θ0 + Real.sin θs)) +
        |xC - xB| * (qn - qm) := by
    intro xB xC
    rw [hpart1]
    simp only [dot2, eucl, incWaveVec, scatWaveVec, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_add, Prod.snd_add, sub_zero, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]
    ring
  have hpart2 : ∀ xB xC : ℝ, xB < xC →
      (doublePathPhaseDiff eps0 ω c θ0 θs qn qm (xB, 0) (xC, 0) = 0 ↔
        Real.sin θs = -Real.sin θ0 - 1 / Real.sqrt eps0 * (c / ω) * (qn - qm)) := by
    intro xB xC hlt
    have hpos : 0 < xC - xB := sub_pos.mpr hlt
    rw [heval, abs_of_pos hpos, ← mul_add, mul_eq_zero]
    simp only [hpos.ne', false_or]
    constructor <;> intro h
    · field_simp [hsq.ne', hω.ne', hc.ne'] at h ⊢
      linarith
    · rw [h]
      field_simp [hsq.ne', hω.ne', hc.ne']
      ring
  refine ⟨hpart1, hpart2, ?_⟩
  constructor
  · rintro ⟨xB, xC, hne, hzero⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := (hpart2 xB xC hlt).mp hzero
      rcases le_or_gt 0 (qn - qm) with hnn | hneg
      · right; rw [abs_of_nonneg hnn]; exact h
      · left; rw [abs_of_neg hneg]; linarith
    · have hpos : 0 < xB - xC := sub_pos.mpr hgt
      rw [heval] at hzero
      have habs : |xC - xB| = xB - xC := by
        rw [abs_of_neg (sub_neg.mpr hgt)]; ring
      rw [habs] at hzero
      have hfac0 : (xB - xC) * (-(Real.sqrt eps0 * (ω / c) * (Real.sin θ0 + Real.sin θs)) + (qn - qm)) = 0 := by
        linarith
      have h0 : -(Real.sqrt eps0 * (ω / c) * (Real.sin θ0 + Real.sin θs)) + (qn - qm) = 0 :=
        (mul_eq_zero.mp hfac0).resolve_left hpos.ne'
      have h : Real.sin θs = -Real.sin θ0 + 1 / Real.sqrt eps0 * (c / ω) * (qn - qm) := by
        field_simp [hsq.ne', hω.ne', hc.ne'] at h0 ⊢
        linarith
      rcases le_or_gt 0 (qn - qm) with hnn | hneg
      · left; rw [abs_of_nonneg hnn]; exact h
      · right; rw [abs_of_neg hneg]; linarith
  · rintro (h | h)
    · rcases le_or_gt 0 (qn - qm) with hnn | hneg
      · rw [abs_of_nonneg hnn] at h
        refine ⟨1, 0, one_ne_zero, ?_⟩
        rw [heval]
        simp only [zero_sub, abs_neg, abs_one]
        rw [h]
        field_simp [hsq.ne', hω.ne', hc.ne']
        ring
      · rw [abs_of_neg hneg] at h
        refine ⟨0, 1, zero_ne_one, ?_⟩
        rw [hpart2 0 1 zero_lt_one]
        linarith
    · rcases le_or_gt 0 (qn - qm) with hnn | hneg
      · rw [abs_of_nonneg hnn] at h
        refine ⟨0, 1, zero_ne_one, ?_⟩
        rw [hpart2 0 1 zero_lt_one]
        exact h
      · rw [abs_of_neg hneg] at h
        refine ⟨1, 0, one_ne_zero, ?_⟩
        rw [heval]
        simp only [zero_sub, abs_neg, abs_one]
        rw [h]
        field_simp [hsq.ne', hω.ne', hc.ne']
        ring
