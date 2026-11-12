-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_fixed_fourier_interval_charfun_power_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:36:48.140221+00:00
-- url     : https://prove2.me/submissions/225128f3-1030-4bbb-b456-484d52749797

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_forces_adjacent_independence_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_adjacent_independent_interval_charfun_concat_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_interval_characteristic_function_power_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- Fixed-grid independence and equal one-step laws give the interval power law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n) (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j))
    (hSame : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
            (t.ofLp i))
    (a k : ℕ) (t : ℝ) :
    MeasureTheory.charFun
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico a (a + k), Y j ω) P) t =
    MeasureTheory.charFun (Measure.map (Y 0) P) t ^ k := by
  let F (u v : ℕ) : ℂ :=
    MeasureTheory.charFun
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico u v, Y j ω) P) t
  let z : ℂ := MeasureTheory.charFun (Measure.map (Y 0) P) t
  have hEmpty (u : ℕ) : F u u = 1 := by
    dsimp [F]
    simp [Finset.Ico_self, MeasureTheory.charFun_dirac]
  have hUnit (u : ℕ) : F u (u + 1) = z := by
    have hSum (ω : Ω) : (∑ j ∈ Finset.Ico u (u + 1), Y j ω) = Y u ω := by
      simpa [Finset.Ico_self] using
        (Finset.sum_Ico_succ_top (le_refl u) (fun j => Y j ω))
    have hEq : (fun ω : Ω => ∑ j ∈ Finset.Ico u (u + 1), Y j ω) = Y u :=
      funext hSum
    change MeasureTheory.charFun
      (Measure.map (fun ω : Ω => ∑ j ∈ Finset.Ico u (u + 1), Y j ω) P) t =
      MeasureTheory.charFun (Measure.map (Y 0) P) t
    rw [hEq, (hSame u 0).map_eq]
  have hConcat (u v w : ℕ) (huv : u ≤ v) (hvw : v ≤ w) :
      F u w = F u v * F v w := by
    exact AvramDividend.Classical.avram_a06_adjacent_independent_interval_charfun_concat_20261111
      P Y hY u v w huv hvw
      (AvramDividend.Classical.avram_a06_fixed_fourier_forces_adjacent_independence_20261111
        P n hn Y hY hFixed u v w huv hvw) t
  exact AvramDividend.Classical.avram_a06_interval_characteristic_function_power_20261111
    F z hEmpty hUnit hConcat a k
