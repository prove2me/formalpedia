-- Prove2me | solution 1 for AvramDividend.Classical.avram_b53_original_finite_grid_gaussian_marked_jump_predictable_gain_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:16:21.095862+00:00
-- url     : https://prove2.me/submissions/bbafd61a-64e2-4f3c-bfec-04f750c01404

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_past_weight_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Genuine finite-grid predictable original Gaussian and compensated marked negative jump source is jointly centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ι)
    (cut : ι → ℕ) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (htT : ∀ i ∈ S, t i ≤ T)
    (ε : ι → ℝ) (hε : ∀ i ∈ S, 0 < ε i)
    (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hBand : ∀ i ∈ S, B i ⊆ Ioo (-1 : ℝ) (-(ε i)))
    (hCut : ∀ i ∈ S,
      B i ⊆ Iic (-(1 / (((cut i : ℕ) : ℝ) + 1))))
    (HG HJ : ι → Ω → ℝ)
    (hHG : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (HG i))
    (hHJM : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (HJ i))
    (hHJ2 : ∀ i ∈ S, MemLp (HJ i) 2 P) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ i ∈ S, Integrable (fun ω =>
        HG i ω * (R (t i) ω - R (s i) ω)) P) →
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let N : ι → Ω → ℝ≥0∞ := fun i ω =>
        NX ω (Ioc (s i) (t i) ×ˢ B i)
      let r : ι → ℝ := fun i =>
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
      let F : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (HG i ω * (R (t i) ω - R (s i) ω) +
          HJ i ω * ((N i ω).toReal - r i))
      Integrable F P ∧ (∫ ω, F ω ∂P) = 0 := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, hRsource, hRmeas, hRI, hRM⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
      X hX hFinite
  refine ⟨R, ?_⟩
  intro hBoth
  rcases hBoth with ⟨hRsrc, hGI⟩
  dsimp only
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let N : ι → Ω → ℝ≥0∞ := fun i ω =>
    NX ω (Ioc (s i) (t i) ×ˢ B i)
  let r : ι → ℝ := fun i =>
    (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
  let cell : ι → Ω → ℝ := fun i ω =>
    HG i ω * (R (t i) ω - R (s i) ω) +
      HJ i ω * ((N i ω).toReal - r i)
  have hc (i : ι) (hi : i ∈ S) :
      Integrable (cell i) P ∧ (∫ ω, cell i ω ∂P) = 0 := by
    have hG0 :=
      avram_jb20_original_gaussian_past_weight_increment_mean_zero
        R hRI hRM (s i) (t i) (hst i hi)
        (HG i) (hHG i hi) (hGI i hi)
    have hJ :=
      avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
        X T (cut i) (s i) (t i) (hst i hi) (htT i hi)
        (ε i) (hε i hi) (B i) (hB i hi)
        (hBand i hi) (hCut i hi)
        (HJ i) (hHJM i hi) (hHJ2 i hi)
    dsimp only at hJ
    refine ⟨(hGI i hi).add hJ.1, ?_⟩
    dsimp only [cell]
    rw [integral_add (hGI i hi) hJ.1, hG0, hJ.2]
    simp
  constructor
  · exact integrable_finset_sum S (fun i hi => (hc i hi).1)
  · rw [integral_finset_sum S (fun i hi => (hc i hi).1)]
    exact Finset.sum_eq_zero (fun i hi => (hc i hi).2)
