-- Prove2me | solution 1 for DeferredInspection.SingleAgent.lemma_1_part_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:58:23.810085+00:00
-- url     : https://prove2.me/submissions/10b73851-ed82-4d30-8760-dea15b744c2a

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

open DeferredInspection.SingleAgent MeasureTheory Set Filter Topology

/-- Comparison principle: if every candidate of `y` at `v` dominates some candidate of `x`,
the optimal payment of `y` dominates that of `x`. -/
private lemma optPay_mono_aux (x y : ℝ → ℝ) (hx : IsAllocation x) (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1)
    (h : ∀ w ∈ Icc 0 v, ∃ u ∈ Icc 0 v,
      v * (x v - x u) + u ≤ v * (y v - y w) + w) :
    optPay x v ≤ optPay y v := by
  have hbdd : BddBelow ((fun w => v * (x v - x w) + w) '' Icc 0 v) := by
    refine ⟨-v, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hx v hv
    have h2 := hx w ⟨hw.1, hw.2.trans hv.2⟩
    simp only [mem_Icc] at h1 h2
    nlinarith [hv.1, hw.1]
  unfold optPay
  apply le_csInf
  · exact ⟨_, ⟨v, ⟨hv.1, le_rfl⟩, rfl⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨u, hu, hle⟩ := h w hw
    exact (csInf_le hbdd ⟨u, hu, rfl⟩).trans hle

theorem solution (x : ℝ → ℝ) (hx : DeferredInspection.SingleAgent.IsAllocation x) :
    (∀ v1 v2, 0 ≤ v1 → v1 < v2 → v2 ≤ 1 → x v2 < x v1 →
      ∀ v ∈ Icc (0 : ℝ) 1, DeferredInspection.SingleAgent.optPay x v ≤
        DeferredInspection.SingleAgent.optPay (Function.update x v2 (x v1)) v) ∧
    (∀ v ∈ Ioc (0 : ℝ) 1, DeferredInspection.SingleAgent.optPay x v ≤
        DeferredInspection.SingleAgent.optPay (Function.update x 0 0) v) ∧
    (∀ v ∈ Icc (0 : ℝ) 1, DeferredInspection.SingleAgent.optPay x v ≤
        DeferredInspection.SingleAgent.optPay (Function.update x 1 1) v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v1 v2 h0 h12 h21 hlt v hv
    apply optPay_mono_aux x _ hx v hv
    intro w hw
    by_cases hvv : v = v2
    · subst hvv
      refine ⟨w, hw, ?_⟩
      by_cases hww : w = v
      · subst hww; simp
      · simp only [Function.update_self, Function.update_of_ne hww]
        nlinarith [hw.1]
    · by_cases hww : w = v2
      · subst hww
        refine ⟨v1, ⟨h0, by linarith [hw.2]⟩, ?_⟩
        simp only [Function.update_self, Function.update_of_ne hvv]
        linarith
      · refine ⟨w, hw, ?_⟩
        simp [Function.update_of_ne hvv, Function.update_of_ne hww]
  · intro v hv
    apply optPay_mono_aux x _ hx v ⟨hv.1.le, hv.2⟩
    intro w hw
    refine ⟨w, hw, ?_⟩
    have hv0 : v ≠ 0 := hv.1.ne'
    by_cases hww : w = 0
    · subst hww
      have := (hx 0 ⟨le_rfl, zero_le_one⟩).1
      simp only [Function.update_self, Function.update_of_ne hv0]
      nlinarith [hv.1]
    · simp [Function.update_of_ne hv0, Function.update_of_ne hww]
  · intro v hv
    apply optPay_mono_aux x _ hx v hv
    intro w hw
    refine ⟨w, hw, ?_⟩
    by_cases hv1 : v = 1
    · subst hv1
      by_cases hww : w = 1
      · subst hww; simp
      · have := (hx 1 ⟨zero_le_one, le_rfl⟩).2
        simp only [Function.update_self, Function.update_of_ne hww]
        linarith
    · have hww : w ≠ 1 := fun h => hv1 (le_antisymm hv.2 (h ▸ hw.2))
      simp [Function.update_of_ne hv1, Function.update_of_ne hww]
