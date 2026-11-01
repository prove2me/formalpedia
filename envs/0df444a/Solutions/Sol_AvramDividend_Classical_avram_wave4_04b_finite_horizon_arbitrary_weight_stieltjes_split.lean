-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:15:48.939382+00:00
-- url     : https://prove2.me/submissions/2b2a2a77-b5a3-4671-a2fd-300d0463bf62

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_exists_atomic_diffuse_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s : ℝ, f s ∂μ) =
      (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
      (∫⁻ s : ℝ, f s ∂μdiffuse) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  have hMass : μ Set.univ = ENNReal.ofReal (rightLimit D T ω) := by
    calc
      μ Set.univ = (dividendMeasure D ω) (Icc (0 : ℝ) (T : ℝ)) := by
        simp [μ]
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
  letI : IsFiniteMeasure μ := ⟨by
    rw [hMass]
    exact ENNReal.ofReal_lt_top⟩
  obtain ⟨A, μatom, μdiffuse, hAcount, hAmeas, hdecomp, hsum, hsupport, hnull⟩ :=
    BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition μ
  have hAtomIntegral :
      (∫⁻ s : ℝ, f s ∂μatom) =
        ∑' t : A, μ {(t : ℝ)} * f (t : ℝ) := by
    rw [hsum, lintegral_sum_measure]
    apply tsum_congr
    intro t
    rw [lintegral_smul_measure, lintegral_dirac]
    rfl
  have hSplit :
      (∫⁻ s : ℝ, f s ∂μ) =
        (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
          (∫⁻ s : ℝ, f s ∂μdiffuse) := by
    calc
      (∫⁻ s : ℝ, f s ∂μ) =
          (∫⁻ s : ℝ, f s ∂(μatom + μdiffuse)) :=
        congrArg (fun ν : Measure ℝ => ∫⁻ s : ℝ, f s ∂ν) hdecomp
      _ = (∫⁻ s : ℝ, f s ∂μatom) +
            (∫⁻ s : ℝ, f s ∂μdiffuse) :=
        lintegral_add_measure f μatom μdiffuse
      _ = (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
            (∫⁻ s : ℝ, f s ∂μdiffuse) := by rw [hAtomIntegral]
  refine ⟨A, μatom, μdiffuse, hAcount, hAmeas,
    hdecomp, hsum, hsupport, hnull, ?_⟩
  change (∫⁻ s : ℝ, f s ∂μ) =
    (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
      (∫⁻ s : ℝ, f s ∂μdiffuse)
  exact hSplit
