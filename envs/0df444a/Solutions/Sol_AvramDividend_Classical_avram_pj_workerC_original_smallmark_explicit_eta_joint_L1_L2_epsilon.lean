-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_smallmark_explicit_eta_joint_L1_L2_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:41:31.453448+00:00
-- url     : https://prove2.me/submissions/febc8992-e687-4cce-a0e7-428ee7f66c22

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_tail_antitone_empty_of_eta_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_negative_smallmark_two_energy_cutoff_epsilon
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (eta : ℕ → ℝ) (hpos : ∀ n, 0 < eta n)
    (hanti : Antitone eta)
    (hlim : Tendsto eta atTop (𝓝 (0 : ℝ))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ,
        (∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in Ioo (-eta n) (0 : ℝ),
            ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) < ENNReal.ofReal ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in Ioo (-eta n) (0 : ℝ),
            ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) <
          ENNReal.ofReal ε := by
  intro Y H HS ε hε
  have htail :=
    AvramDividend.Classical.avram_pj_workerC_negative_tail_antitone_empty_of_eta_tendsto
      eta hpos hanti hlim
  have hBMeas : ∀ n : ℕ, MeasurableSet (Ioo (-eta n) (0 : ℝ)) := by
    intro n
    exact measurableSet_Ioo
  have hBNeg : ∀ n : ℕ, Ioo (-eta n) (0 : ℝ) ⊆ Iio (0 : ℝ) := by
    intro n z hz
    exact hz.2
  exact
    AvramDividend.Classical.avram_pj_workerC_actual_negative_smallmark_two_energy_cutoff_epsilon
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ (fun n => Ioo (-eta n) (0 : ℝ))
      hBMeas hBNeg htail.1 htail.2 ε hε

