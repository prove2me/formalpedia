-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_finite_reciprocal_grid_integrable_measurable_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:27:53.68018+00:00
-- url     : https://prove2.me/submissions/555550dc-53cf-4a74-b431-c6fc56ec0cf8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_past_count_raw_measurable
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_reciprocal_band_count_L1_Campbell_20261122
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
    Measurable S ∧ Integrable S P := by
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
  change Measurable S ∧ Integrable S P
  have hCountMeas : ∀ i : ℕ,
      Measurable (fun ω => NX ω (Ioc 0 T ×ˢ B i)) := by
    intro i
    have h := avram_a20_original_borel_past_count_raw_measurable
      X T (B i) measurableSet_Ioc
    exact h.mono (𝓕.le T) le_rfl
  have hCountReal : ∀ i : ℕ,
      Measurable (fun ω => (NX ω (Ioc 0 T ×ˢ B i)).toReal) := by
    intro i
    exact (hCountMeas i).ennreal_toReal
  have hMeas : Measurable S := by
    dsimp [S]
    exact Finset.measurable_sum _ (fun i hi =>
      measurable_const.mul ((hCountReal i).sub measurable_const))
  have hCountI : ∀ i : ℕ,
      Integrable (fun ω => (NX ω (Ioc 0 T ×ˢ B i)).toReal) P := by
    intro i
    have h := avram_twoagentA_public_original_reciprocal_band_count_L1_Campbell_20261122
      X T i (i + 1)
    simpa [B, NX, Nat.cast_succ, add_assoc, one_add_one_eq_two] using h.1
  refine ⟨hMeas, ?_⟩
  dsimp [S]
  apply integrable_finset_sum
  intro i hi
  exact ((hCountI i).sub (integrable_const (r i))).const_mul
    (-(1 / ((i : ℝ) + 1)))
