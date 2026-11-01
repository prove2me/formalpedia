-- Prove2me | solution 1 for DeferredInspection.SingleAgent.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:57:46.158358+00:00
-- url     : https://prove2.me/submissions/fe0d3ff0-50de-43e2-890b-039d47fd76a0

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

open DeferredInspection.SingleAgent MeasureTheory Set Filter Topology

theorem solution (x p : ℝ → ℝ) (hx : DeferredInspection.SingleAgent.IsAllocation x) :
    (DeferredInspection.SingleAgent.IsIC x p → ∀ v ∈ Icc (0 : ℝ) 1, p v ≤ DeferredInspection.SingleAgent.optPay x v) ∧
    (x 0 = 0 → DeferredInspection.SingleAgent.IsIC x (DeferredInspection.SingleAgent.optPay x) ∧
      DeferredInspection.SingleAgent.IsIR x (DeferredInspection.SingleAgent.optPay x)) := by
  have hbdd : ∀ v ∈ Icc (0:ℝ) 1, BddBelow ((fun w => v * (x v - x w) + w) '' Icc 0 v) := by
    intro v hv
    refine ⟨-v, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hx v hv
    have h2 := hx w ⟨hw.1, hw.2.trans hv.2⟩
    simp only [mem_Icc] at h1 h2
    nlinarith [hv.1, hw.1]
  refine ⟨fun hIC v hv => ?_, fun h0 => ?_⟩
  · unfold optPay
    apply le_csInf
    · exact ⟨_, ⟨v, ⟨hv.1, le_rfl⟩, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      have := hIC v hv w ⟨hw.1, hw.2.trans hv.2⟩
      linarith
  · have hle0 : ∀ v ∈ Icc (0:ℝ) 1, optPay x v ≤ v * x v := by
      intro v hv
      have := csInf_le (hbdd v hv) ⟨0, ⟨le_rfl, hv.1⟩, rfl⟩
      simpa [optPay, h0] using this
    have hlev : ∀ v ∈ Icc (0:ℝ) 1, optPay x v ≤ v := by
      intro v hv
      have := csInf_le (hbdd v hv) ⟨v, ⟨hv.1, le_rfl⟩, rfl⟩
      simpa [optPay] using this
    refine ⟨fun v hv w hw => ?_, fun v hv => ?_⟩
    · rcases le_or_gt w v with hwv | hwv
      · have := csInf_le (hbdd v hv) ⟨w, ⟨hw.1, hwv⟩, rfl⟩
        simp only [optPay] at this ⊢
        linarith
      · have h1 := hle0 v hv
        have h2 := hx w hw
        simp only [mem_Icc] at h2
        nlinarith [hv.1]
    · linarith [hle0 v hv]
