-- Prove2me | solution 1 for DeferredInspection.SingleAgent.lemma_1_part_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:19:22.369913+00:00
-- url     : https://prove2.me/submissions/cbf8ba97-e66d-4aec-8862-8b0969b9545c

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

open DeferredInspection.SingleAgent MeasureTheory Set Filter Topology

namespace DIL12

variable {x : ℝ → ℝ} (hx : IsAllocation x)
include hx

lemma hullset_nonempty (v : ℝ) : {y | ∃ g : ℝ → ℝ, ConcaveOn ℝ (Icc 0 1) g ∧
    (∀ w ∈ Icc (0 : ℝ) 1, x w ≤ g w) ∧ y = g v}.Nonempty :=
  ⟨1, fun _ => 1, concaveOn_const 1 (convex_Icc 0 1), fun w hw => (hx w hw).2, rfl⟩

lemma hullset_bdd {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : BddBelow {y | ∃ g : ℝ → ℝ,
    ConcaveOn ℝ (Icc 0 1) g ∧ (∀ w ∈ Icc (0 : ℝ) 1, x w ≤ g w) ∧ y = g v} := by
  refine ⟨x v, ?_⟩
  rintro _ ⟨g, -, hg, rfl⟩
  exact hg v hv

lemma hull_le {g : ℝ → ℝ} (hgc : ConcaveOn ℝ (Icc 0 1) g) (hg : ∀ w ∈ Icc (0 : ℝ) 1, x w ≤ g w)
    {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : concaveHull x v ≤ g v :=
  csInf_le (hullset_bdd hx hv) ⟨g, hgc, hg, rfl⟩

lemma le_hull {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : x v ≤ concaveHull x v := by
  apply le_csInf (hullset_nonempty hx v)
  rintro _ ⟨g, -, hg, rfl⟩
  exact hg v hv

lemma hull_concave : ConcaveOn ℝ (Icc 0 1) (concaveHull x) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro a ha b hb α β hα hβ hαβ
  have hab : α • a + β • b ∈ Icc (0:ℝ) 1 := convex_Icc 0 1 ha hb hα hβ hαβ
  apply le_csInf (hullset_nonempty hx _)
  rintro _ ⟨g, hgc, hg, rfl⟩
  have h1 := hull_le hx hgc hg ha
  have h2 := hull_le hx hgc hg hb
  have h3 := hgc.2 ha hb hα hβ hαβ
  simp only [smul_eq_mul] at h3 ⊢
  nlinarith

end DIL12

theorem solution (x : ℝ → ℝ) (hx : DeferredInspection.SingleAgent.IsAllocation x) :
    ConcaveOn ℝ (Icc 0 1) (DeferredInspection.SingleAgent.concaveHull x) ∧
    ∀ v ∈ Icc (0 : ℝ) 1, DeferredInspection.SingleAgent.optPay x v ≤
      DeferredInspection.SingleAgent.optPay (DeferredInspection.SingleAgent.concaveHull x) v := by
  refine ⟨DIL12.hull_concave hx, ?_⟩
  intro v hv
  have hbdd : BddBelow ((fun w => v * (x v - x w) + w) '' Icc 0 v) := by
    refine ⟨-v, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hx v hv
    have h2 := hx w ⟨hw.1, hw.2.trans hv.2⟩
    simp only [mem_Icc] at h1 h2
    nlinarith [hv.1, hw.1]
  unfold optPay
  apply le_csInf ((nonempty_Icc.2 hv.1).image _)
  rintro _ ⟨w, hw, rfl⟩
  rcases hv.1.lt_or_eq with hv0 | hv0
  · -- `φ = sup_{u ∈ [0,1]} (v x(u) - u)`
    set φ := sSup ((fun u => v * x u - u) '' Icc 0 1) with hφ
    have hbddA : BddAbove ((fun u => v * x u - u) '' Icc 0 1) := by
      refine ⟨v, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      have := hx u hu
      nlinarith [this.2, hu.1]
    have hA : sInf ((fun w => v * (x v - x w) + w) '' Icc 0 v) ≤ v * x v - φ := by
      have hle0 : sInf ((fun w => v * (x v - x w) + w) '' Icc 0 v) ≤ v * x v := by
        have := csInf_le hbdd ⟨0, ⟨le_rfl, hv.1⟩, rfl⟩
        have h0 := (hx 0 ⟨le_rfl, zero_le_one⟩).1
        simp only at this
        nlinarith
      have : φ ≤ v * x v - sInf ((fun w => v * (x v - x w) + w) '' Icc 0 v) := by
        apply csSup_le ((nonempty_Icc.2 zero_le_one).image _)
        rintro _ ⟨u, hu, rfl⟩
        rcases le_or_gt u v with huv | huv
        · have := csInf_le hbdd ⟨u, ⟨hu.1, huv⟩, rfl⟩
          simp only at this ⊢
          linarith
        · have := (hx u hu).2
          simp only
          nlinarith
      linarith
    have hB : v * concaveHull x w - w ≤ φ := by
      have hL : ConcaveOn ℝ (Icc 0 1) (fun u => (φ + u) / v) := by
        refine ⟨convex_Icc 0 1, ?_⟩
        intro a _ b _ α β _ _ hαβ
        simp only [smul_eq_mul]
        apply le_of_eq
        have : β = 1 - α := by linarith
        subst this
        field_simp
        ring
      have hLx : ∀ u ∈ Icc (0:ℝ) 1, x u ≤ (φ + u) / v := by
        intro u hu
        rw [le_div_iff₀ hv0]
        have := le_csSup hbddA ⟨u, hu, rfl⟩
        simp only at this
        linarith
      have := DIL12.hull_le hx hL hLx ⟨hw.1, hw.2.trans hv.2⟩
      rw [le_div_iff₀ hv0] at this
      linarith
    have hC := DIL12.le_hull hx hv
    simp only
    nlinarith
  · subst hv0
    have hw0 : w = 0 := le_antisymm hw.2 hw.1
    subst hw0
    have := csInf_le hbdd ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩
    simp only [zero_mul, add_zero] at this ⊢
    exact this
