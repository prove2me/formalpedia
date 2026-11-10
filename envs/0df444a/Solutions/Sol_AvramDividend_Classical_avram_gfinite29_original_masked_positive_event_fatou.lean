-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite29_original_masked_positive_event_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T04:06:58.143506+00:00
-- url     : https://prove2.me/submissions/1971a825-add6-4022-92fb-b02b10f185e6

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_natural_clock_fatou_L1_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Positive-clock event masks preserve the a.e. stopped reward Fatou budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (σ : Ω → ℝ≥0) (hσmeas : Measurable σ)
    (L : ℕ → Ω → ℝ≥0) (hLmeas : ∀ j, Measurable (L j)) (hLle : ∀ j ω, L j ω ≤ σ ω)
    (hLlim : ∀ᵐ ω ∂P, Tendsto (fun j => L j ω) atTop (𝓝 (σ ω)))
    (H : (Ω → ℝ≥0) → Ω → ℝ) (hHmeas : ∀ j, Measurable (H (L j))) (hHσmeas : AEStronglyMeasurable (H σ) P) (hHInt : ∀ j, Integrable (H (L j)) P)
    (hHpos : ∀ j ω, L j ω ≠ 0 → 0 ≤ H (L j) ω) (hHσpos : ∀ ω, σ ω ≠ 0 → 0 ≤ H σ ω)
    (hHlim : ∀ᵐ ω ∂P, Tendsto (fun j => ENNReal.ofReal (H (L j) ω)) atTop (𝓝 (ENNReal.ofReal (H σ ω))))
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ j, (∫ ω in A ∩ {η : Ω | L j η ≠ 0}, H (L j) ω ∂P) ≤ b) :
    (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, H σ ω ∂P) ≤ b := by
  classical
  let E : (Ω → ℝ≥0) → Set Ω := fun ζ => A ∩ {ω : Ω | ζ ω ≠ 0}
  have hEmeas (ζ : Ω → ℝ≥0) (hζ : Measurable ζ) :
      MeasurableSet (E ζ) := by
    have hz : MeasurableSet {ω : Ω | ζ ω = 0} := hζ (measurableSet_singleton (0 : ℝ≥0))
    have hnz : MeasurableSet {ω : Ω | ζ ω ≠ 0} := by simpa only [Set.compl_setOf] using hz.compl
    exact hA.inter hnz
  let F : ℕ → Ω → ℝ := fun j ω => if ω ∈ E (L j) then H (L j) ω else 0
  let S : Ω → ℝ := fun ω => if ω ∈ E σ then H σ ω else 0
  have hF_eq (j : ℕ) : F j = (E (L j)).indicator (H (L j)) := by funext ω; simp [F, Set.indicator]
  have hS_eq : S = (E σ).indicator (H σ) := by funext ω; simp [S, Set.indicator]
  have hFm (j : ℕ) : Measurable (F j) := Measurable.ite (hEmeas (L j) (hLmeas j)) (hHmeas j) measurable_const
  have hFi (j : ℕ) : Integrable (F j) P := by
    rw [hF_eq j]
    exact (hHInt j).indicator (hEmeas (L j) (hLmeas j))
  have hFpos (j : ℕ) : 0 ≤ᵐ[P] F j := by
    change ∀ᵐ ω ∂P, (0 : ℝ) ≤ F j ω
    filter_upwards [] with ω
    by_cases he : ω ∈ E (L j)
    · simpa [F, he] using hHpos j ω he.2
    · simp [F, he]
  have hSm : AEStronglyMeasurable S P := by
    rw [hS_eq]
    exact hHσmeas.indicator (hEmeas σ hσmeas)
  have hSpos : 0 ≤ᵐ[P] S := by
    change ∀ᵐ ω ∂P, (0 : ℝ) ≤ S ω
    filter_upwards [] with ω
    by_cases he : ω ∈ E σ
    · simpa [S, he] using hHσpos ω he.2
    · simp [S, he]
  have hFbudget (j : ℕ) : (∫ ω, F j ω ∂P) ≤ b := by
    rw [hF_eq j]
    rw [integral_indicator (hEmeas (L j) (hLmeas j))]
    exact hBudget j
  have hFlim : ∀ᵐ ω ∂P, Tendsto (fun j => ENNReal.ofReal (F j ω)) atTop
      (𝓝 (ENNReal.ofReal (S ω))) := by
    filter_upwards [hLlim, hHlim] with ω hClock hReward
    by_cases ha : ω ∈ A
    · by_cases hz : σ ω = 0
      · have hLj : ∀ j, L j ω = 0 := by
          intro j
          exact le_antisymm (by simpa [hz] using hLle j ω) zero_le
        have hFz : ∀ j, F j ω = 0 := fun j => by simp [F, E, hLj j]
        have hSz : S ω = 0 := by simp [S, E, hz]
        simpa [hFz, hSz] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      · have hpos : 0 < σ ω := pos_iff_ne_zero.mpr hz
        have hEventually : ∀ᶠ j in atTop, L j ω ≠ 0 := (hClock.eventually (Ioi_mem_nhds hpos)).mono (fun j hj => ne_of_gt hj)
        have hEq : (fun j => ENNReal.ofReal (F j ω)) =ᶠ[atTop] (fun j => ENNReal.ofReal (H (L j) ω)) := by
          filter_upwards [hEventually] with j hj
          simp [F, E, ha, hj]
        have hSval : S ω = H σ ω := by simp [S, E, ha, hz]
        simpa [hSval] using hReward.congr' hEq.symm
    · have hFz : ∀ j, F j ω = 0 := fun j => by simp [F, E, ha]
      have hSz : S ω = 0 := by simp [S, E, ha]
      simpa [hFz, hSz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  have hBound := (avram_p4_f4_ae_natural_clock_fatou_L1_budget
    P S F hSm hSpos hFm hFi hFpos hFlim b hb hFbudget).2
  rw [hS_eq] at hBound
  rw [integral_indicator (hEmeas σ hσmeas)] at hBound
  exact hBound
