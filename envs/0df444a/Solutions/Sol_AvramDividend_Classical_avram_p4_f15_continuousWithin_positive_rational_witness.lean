-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f15_continuousWithin_positive_rational_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:58:48.216204+00:00
-- url     : https://prove2.me/submissions/c49b92ed-1032-49a7-9406-9d905dc4760c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- A positive right-continuous value remains positive at a rational time
strictly between the observation time and any later deadline. -/
theorem solution
    (f : ℝ≥0 → ℝ) (s ε : ℝ≥0)
    (hsε : s < ε) (hpos : 0 < f s)
    (hcont : ContinuousWithinAt f (Ici s) s) :
    ∃ q : ℚ≥0, s < (q : ℝ≥0) ∧ (q : ℝ≥0) < ε ∧ 0 < f (q : ℝ≥0) := by
  have hEv : ∀ᶠ t : ℝ≥0 in 𝓝 s, t ∈ Ici s → 0 < f t :=
    eventually_nhdsWithin_iff.mp
      (hcont.eventually (isOpen_Ioi.mem_nhds hpos))
  have hMem : {t : ℝ≥0 | t ∈ Ici s → 0 < f t} ∈ 𝓝 s := hEv
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp hMem
  let d : ℝ≥0 := ⟨δ / 2, by positivity⟩
  have hd0 : 0 < d := by
    change (0 : ℝ) < δ / 2
    linarith
  let u : ℝ≥0 := min ε (s + d)
  have hsu : s < u := lt_min hsε (lt_add_of_pos_right _ hd0)
  obtain ⟨r, hr0, hsr, hru⟩ := (NNReal.lt_iff_exists_rat_btwn s u).mp hsu
  let q : ℚ≥0 := ⟨r, hr0⟩
  have hq_eq : (q : ℝ≥0) = (r : ℝ).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by exact_mod_cast hr0)]
    norm_cast
  have hsq : s < (q : ℝ≥0) := by simpa only [hq_eq] using hsr
  have hqu : (q : ℝ≥0) < u := by simpa only [hq_eq] using hru
  have hqε : (q : ℝ≥0) < ε :=
    lt_of_lt_of_le hqu (min_le_left ε (s + d))
  have hqsd : (q : ℝ≥0) < s + d :=
    lt_of_lt_of_le hqu (min_le_right ε (s + d))
  have hreal : ((q : ℝ≥0) : ℝ) < (s : ℝ) + (d : ℝ) := by
    exact_mod_cast hqsd
  have hqδ : ((q : ℝ≥0) : ℝ) - (s : ℝ) < δ := by
    have : (d : ℝ) = δ / 2 := rfl
    linarith
  have hnonneg : 0 ≤ ((q : ℝ≥0) : ℝ) - (s : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast hsq.le)
  have hdist : dist (q : ℝ≥0) s < δ := by
    rw [NNReal.dist_eq, abs_of_nonneg hnonneg]
    exact hqδ
  have hqPos : 0 < f (q : ℝ≥0) :=
    hball (by simpa only [Metric.mem_ball] using hdist) (Set.mem_Ici.mpr hsq.le)
  exact ⟨q, hsq, hqε, hqPos⟩

