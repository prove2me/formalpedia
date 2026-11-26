-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.approximate_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:48:39.122379+00:00
-- url     : https://prove2.me/submissions/8b9e797f-26b5-407f-9202-1122051c48ec

import Mathlib

open Set

set_option maxHeartbeats 600000 in
theorem solution (x l : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (δ : ℝ) (hδ : 0 ≤ δ)
    (hx₀ : x 0 = 0) (hx : BddBelow (Set.range (fun s : Set.Icc (0 : ℝ) t => x s)))
    (hl₀ : l 0 = 0) (hlc : ContinuousOn l (Set.Icc 0 t))
    (hlm : MonotoneOn l (Set.Icc 0 t))
    (hnon : ∀ s ∈ Set.Icc 0 t, 0 ≤ x s + l s)
    (hflat : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t →
      (∀ s ∈ Set.Ioc a b, δ < x s + l s) → l b = l a) :
    let v := -(⨅ s : Set.Icc (0 : ℝ) t, x s)
    v ≤ l t ∧ l t ≤ v + δ := by
  let m := ⨅ s : Icc (0 : ℝ) t, x s
  have h0 : (0:ℝ) ∈ Icc 0 t := ⟨le_rfl,ht⟩
  have ht' : t ∈ Icc 0 t := ⟨ht,le_rfl⟩
  have h0m : m ≤ 0 := (ciInf_le hx ⟨0,h0⟩).trans_eq hx₀
  letI : Nonempty (Icc (0:ℝ) t) := ⟨⟨0,h0⟩⟩
  change -m ≤ l t ∧ l t ≤ -m + δ
  constructor
  · have hL : -l t ≤ m := by
      apply le_ciInf
      intro s
      have hq := hnon s s.2
      have hl := hlm s.2 ht' s.2.2
      linarith
    linarith
  · by_contra! h
    let z := (-m + δ + l t)/2
    have hz : -m+δ < z := by dsimp [z]; linarith
    have hz' : z < l t := by dsimp [z]; linarith
    have hL0 : l 0 ≤ z := by rw [hl₀]; linarith
    obtain ⟨a,ha,haz⟩ := intermediate_value_Icc ht hlc
      (show z ∈ Icc (l 0) (l t) from ⟨hL0,hz'.le⟩)
    have hFlat := hflat a t ha.1 ha.2 le_rfl (fun s hs => by
      have hs' : s ∈ Icc 0 t := ⟨ha.1.trans hs.1.le,hs.2⟩
      have hxs : m ≤ x s := ciInf_le hx ⟨s,hs'⟩
      have hls := (hlm ha hs' hs.1.le)
      linarith)
    linarith
