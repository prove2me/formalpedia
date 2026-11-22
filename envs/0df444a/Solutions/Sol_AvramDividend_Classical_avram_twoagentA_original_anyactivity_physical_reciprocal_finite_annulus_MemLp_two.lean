-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_anyactivity_physical_reciprocal_finite_annulus_MemLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:38:30.541098+00:00
-- url     : https://prove2.me/submissions/54f60208-2055-4e87-85f5-ad2939f51350

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_past_count_raw_measurable
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let S : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    Measurable S ∧ MemLp S 2 P := by
  classical
  let B : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let S : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.Ico n m,
      (-(1 / ((i : ℝ) + 1))) *
        ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
  have hNM (i : ℕ) :
      Measurable (fun ω : Ω => (NX ω (Ioc 0 T ×ˢ B i)).toReal) := by
    have hN :=
      avram_a20_original_borel_past_count_raw_measurable
        X T (B i) measurableSet_Ioc
    exact ENNReal.measurable_toReal.comp (hN.mono (𝓕.le T) le_rfl)
  have hSM : Measurable S := by
    dsimp [S]
    apply Finset.measurable_sum
    intro i hi
    exact measurable_const.mul ((hNM i).sub measurable_const)
  have hS2 : Integrable (fun ω => (S ω) ^ 2) P := by
    simpa only [S, B, NX, r] using
      (avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
        X T n m hnm)
  have hL2 : MemLp S 2 P :=
    (memLp_two_iff_integrable_sq hSM.aestronglyMeasurable).mpr hS2
  exact ⟨hSM, hL2⟩
