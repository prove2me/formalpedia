-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_negative_Borel_grid_occupied_indicator_iid_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:24:30.961126+00:00
-- url     : https://prove2.me/submissions/8b3d72e7-93ea-40e9-aa58-1e99c5953402

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_Borel_physical_equal_grid_cell_counts_jointly_independent_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_shifted_Borel_physical_occupancy_event_stationary_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    let Y : Fin n → Ω → ℕ := fun i ω =>
      if NX ω (Ioc ((i.val : ℝ≥0) * δ)
        (((i.val + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B) = 0
      then 0 else 1
    (∀ i, Measurable (Y i)) ∧
      iIndepFun Y P ∧
      ∀ i : Fin n, P {ω : Ω | Y i ω = 1} =
        P {ω : Ω | NX ω (Ioc 0 δ ×ˢ B) ≠ 0} := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let δ : ℝ≥0 := T / (n : ℝ≥0)
  let C : Fin n → Ω → ℝ≥0∞ := fun i ω =>
    NX ω (Ioc ((i.val : ℝ≥0) * δ)
      (((i.val + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B)
  let Y : Fin n → Ω → ℕ := fun i ω => if C i ω = 0 then 0 else 1
  change (∀ i, Measurable (Y i)) ∧
    iIndepFun Y P ∧
    ∀ i, P {ω : Ω | Y i ω = 1} =
      P {ω : Ω | NX ω (Ioc 0 δ ×ˢ B) ≠ 0}
  let g : ℝ≥0∞ → ℕ := fun z => if z = 0 then 0 else 1
  have hg : Measurable g := by
    exact measurable_const.ite (measurableSet_singleton (0 : ℝ≥0∞)) measurable_const
  have hCMeas (i : Fin n) : Measurable (C i) := by
    have hle : (i.val : ℝ≥0) * δ ≤
        (((i.val + 1 : ℕ) : ℝ≥0) * δ) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i.val) bot_le
    simpa only [C, NX] using
      (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X ((i.val : ℝ≥0) * δ)
        (((i.val + 1 : ℕ) : ℝ≥0) * δ) hle B hB)
  have hCInd : iIndepFun C P := by
    simpa only [C, NX, δ] using
      (avram_a27_original_negative_Borel_physical_equal_grid_cell_counts_jointly_independent_20261116
        X T B hB n)
  have hInd : iIndepFun Y P := by
    have hh := hCInd.comp (fun _ => g) (fun _ => hg)
    simpa only [Y, C, g, Function.comp_def] using hh
  refine ⟨?_, hInd, ?_⟩
  · intro i
    have hh := hg.comp (hCMeas i)
    simpa only [Y, C, g, Function.comp_def] using hh
  · intro i
    have hq : ((i.val + 1 : ℕ) : ℝ≥0) * δ =
        (i.val : ℝ≥0) * δ + δ := by
      simp [Nat.cast_add, add_mul]
    have hLaw :=
      avram_a27_original_shifted_Borel_physical_occupancy_event_stationary_20261116
        X ((i.val : ℝ≥0) * δ) δ B hB
    have hEvent : {ω : Ω | Y i ω = 1} =
        {ω : Ω | C i ω ≠ 0} := by
      ext ω
      simp [Y, g]
    rw [hEvent]
    simpa only [C, NX, hq] using hLaw
