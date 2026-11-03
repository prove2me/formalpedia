-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:33:21.711694+00:00
-- url     : https://prove2.me/submissions/697f9e69-92d8-45f9-a0ff-4065c3aa3da4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

noncomputable section

/-- The original stopped Stieltjes cash is exactly a countable sum of its
pre-ruin right atoms plus its actual stopped atomless component; the literal
paymentTimes convention includes time zero and excludes positive ruin atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ((∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ) =
        (∑' t : A, μ {(t : ℝ)} * (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω) then
            ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) else 0)) +
        (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μdiffuse)) ∧
      ((∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ) ≤
        ENNReal.ofReal (rightLimit D T ω)) := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  rcases avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
    X x D hD ω T
    (fun s : ℝ => (if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * s))) else 0)) with
    ⟨A, μdiffuse, hCount, hMeas, hNull, hAt, hSupport, hFull⟩
  refine ⟨A, μdiffuse, hCount, hMeas, hNull, hAt, hSupport, hFull, ?_⟩
  have hFullCash :
      (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
        ENNReal.ofReal (rightLimit D T ω) :=
    avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
      q hq D hD ω T
  have hStopLe :
      (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ) ≤
      (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) := by
    apply lintegral_mono
    intro s
    by_cases hs : s ∈ paymentTimes (ruinTime X x D ω)
    · simp [hs]
    · simp [hs]
  exact le_trans hStopLe hFullCash
