-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_countable_finite_negative_support_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:43:23.256852+00:00
-- url     : https://prove2.me/submissions/e3caacea-d262-4bfa-b366-dee8bf696693

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Every negative-supported measure finite on bands separated from zero
has a concrete countable cover by measurable finite-measure sets. -/
theorem solution
    (μ : Measure ℝ)
    (hzero : μ (Ici (0 : ℝ)) = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → μ (Iic (-ε)) < ⊤) :
    ∃ C : ℕ → Set ℝ,
      (∀ n, MeasurableSet (C n)) ∧
      (∀ n, μ (C n) < ⊤) ∧
      (⋃ n, C n) = univ := by
  let C : ℕ → Set ℝ
    | 0 => Ici 0
    | n + 1 => Iic (-(1 / ((n : ℝ) + 1)))
  have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlim : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using hbase.neg
  refine ⟨C, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact measurableSet_Ici
    | succ n => exact measurableSet_Iic
  · intro n
    cases n with
    | zero =>
        change μ (Ici (0 : ℝ)) < ⊤
        simpa only [hzero] using (ENNReal.zero_lt_top)
    | succ n =>
        change μ (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤
        exact hfin _ (by positivity)
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      by_cases hx : 0 ≤ x
      · exact Set.mem_iUnion.mpr ⟨0, hx⟩
      · have hxneg : x < (0 : ℝ) := lt_of_not_ge hx
        have hN : Ioi x ∈ 𝓝 (0 : ℝ) :=
          isOpen_Ioi.mem_nhds hxneg
        obtain ⟨n, hn⟩ := (hlim.eventually hN).exists
        exact Set.mem_iUnion.mpr ⟨n + 1, le_of_lt hn⟩
