-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_finite_compact_test_mark_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:35:32.770694+00:00
-- url     : https://prove2.me/submissions/ef3b1153-f73f-4389-a5f2-7e2bc5944dc8

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_test_jump_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_intrinsic_nonnegative_test_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
/-- Genuine finite compact negative marked-jump integral representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0)
    (g : ℝ → ℝ) (hg : Continuous g)
    (ε : ℝ) (hε : 0 < ε)
    (hvanish : ∀ y : ℝ, dist y 0 < ε → g y = 0) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        g (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
      (∫⁻ p : ℝ≥0 × ℝ,
        (if p.1 ∈ Ioc (0 : ℝ≥0) T then
          ENNReal.ofReal (g p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 =>
            (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
        ∑ u ∈ F, ENNReal.ofReal (g (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
  classical
  let S : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    g (X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}
  have hfinite : S.Finite :=
    avram_p2_a_zero_rate_original_test_jump_times_finite X ω T ε hε g hvanish
  let F : Finset ℝ≥0 := hfinite.toFinset
  have hF (u : ℝ≥0) : u ∈ F ↔ u ∈ S := by
    exact hfinite.mem_toFinset
  have hmeas : Measurable
      (fun p : ℝ≥0 × ℝ =>
        if p.1 ∈ Ioc (0 : ℝ≥0) T then
          ENNReal.ofReal (g p.2) else 0) := by
    exact Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
      (ENNReal.measurable_ofReal.comp (hg.measurable.comp measurable_snd))
      measurable_const
  have hzero (u : ℝ≥0) (hu : u ∉ F) :
      ({v : ℝ≥0 | 0 < v ∧ X.X v ω -
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).indicator
        (fun v : ℝ≥0 => if v ∈ Ioc (0 : ℝ≥0) T then
          ENNReal.ofReal (g (X.X v ω -
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v)) else 0) u = 0 := by
    by_cases hj : 0 < u ∧ X.X u ω -
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0
    · by_cases ht : u ≤ T
      · have hg0 : g (X.X u ω -
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u) = 0 := by
          by_contra hneq
          exact hu ((hF u).2 ⟨hj.1, ht, hneq⟩)
        simp [Set.indicator, hj, hj.1, ht, hg0]
      · simp [Set.indicator, hj, ht]
    · simp [Set.indicator, hj]
  have hg0 : g 0 = 0 := by
    apply hvanish 0
    simpa using hε
  refine ⟨F, (by intro u; simpa only [S, Set.mem_setOf_eq] using hF u), ?_⟩
  rw [avram_p2_a_zero_rate_original_intrinsic_nonnegative_test_lintegral
    X ω (fun p : ℝ≥0 × ℝ =>
      if p.1 ∈ Ioc (0 : ℝ≥0) T then
        ENNReal.ofReal (g p.2) else 0) hmeas]
  rw [tsum_eq_sum (s := F) hzero]
  apply Finset.sum_congr rfl
  intro u hu
  have hs : u ∈ S := (hF u).1 hu
  have hdelta : X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    intro hz
    exact hs.2.2 (by simpa [hz] using hg0)
  simp [Set.indicator, hs.1, hs.2.1, hdelta]
