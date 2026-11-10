-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:21:57.579644+00:00
-- url     : https://prove2.me/submissions/a38b2d17-651a-4a10-9e8d-e63a19343220

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf13_original_threecut_annulus_real_additivity
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Disjoint adjacent physical negative-annulus compensated counts have zero covariance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) :
    let B : ℕ → ℕ → Set ℝ := fun a b =>
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B a b)
    let r : ℕ → ℕ → ℝ := fun a b =>
      ((T : ℝ≥0∞) * X.ν (B a b)).toReal
    Integrable (fun ω =>
      ((N n m ω).toReal - r n m) *
      ((N m p ω).toReal - r m p)) P ∧
    (∫ ω, ((N n m ω).toReal - r n m) *
      ((N m p ω).toReal - r m p) ∂P) = 0 := by
  classical
  let B : ℕ → ℕ → Set ℝ := fun a b =>
    Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
  let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B a b)
  let r : ℕ → ℕ → ℝ := fun a b =>
    ((T : ℝ≥0∞) * X.ν (B a b)).toReal
  change Integrable (fun ω =>
    ((N n m ω).toReal - r n m) *
    ((N m p ω).toReal - r m p)) P ∧
    (∫ ω, ((N n m ω).toReal - r n m) *
      ((N m p ω).toReal - r m p) ∂P) = 0
  have hVNM := avram_mixed_source13_original_physical_annulus_count_variance_exact
    X T n m hnm
  have hVMP := avram_mixed_source13_original_physical_annulus_count_variance_exact
    X T m p hmp
  have hVNP := avram_mixed_source13_original_physical_annulus_count_variance_exact
    X T n p (le_trans hnm hmp)
  change Integrable (fun ω => ((N n m ω).toReal - r n m) ^ 2) P ∧
    (∫ ω, ((N n m ω).toReal - r n m) ^ 2 ∂P) = r n m at hVNM
  change Integrable (fun ω => ((N m p ω).toReal - r m p) ^ 2) P ∧
    (∫ ω, ((N m p ω).toReal - r m p) ^ 2 ∂P) = r m p at hVMP
  change Integrable (fun ω => ((N n p ω).toReal - r n p) ^ 2) P ∧
    (∫ ω, ((N n p ω).toReal - r n p) ^ 2 ∂P) = r n p at hVNP
  let R : ℕ → ℝ := fun j =>
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((j : ℝ) + 1))))).toReal
  have hRM := avram_mixed_source13_original_annulus_levy_rate_difference
    X T n m hnm
  have hRP := avram_mixed_source13_original_annulus_levy_rate_difference
    X T m p hmp
  have hRNP := avram_mixed_source13_original_annulus_levy_rate_difference
    X T n p (le_trans hnm hmp)
  change R m = R n + r n m at hRM
  change R p = R m + r m p at hRP
  change R p = R n + r n p at hRNP
  have hRateAdd : r n p = r n m + r m p := by linarith
  have hCount :=
    avram_mix_inf13_original_threecut_annulus_real_additivity
      X T n m p hnm hmp
  change ∀ ω, (N n p ω).toReal =
    (N n m ω).toReal + (N m p ω).toReal at hCount
  have hPhi (ω : Ω) :
      (N n p ω).toReal - r n p =
      ((N n m ω).toReal - r n m) +
      ((N m p ω).toReal - r m p) := by
    rw [hCount ω, hRateAdd]
    ring
  have hSepNM : B n m ⊆ Iic (-(1 / ((m : ℝ) + 1))) := by
    intro z hz
    exact hz.2
  have hSepMP : B m p ⊆ Iic (-(1 / ((p : ℝ) + 1))) := by
    intro z hz
    exact hz.2
  have hLpNM : MemLp (fun ω => (N n m ω).toReal - r n m) 2 P := by
    simpa only [N, r, B, tsub_zero] using
      (avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T m 0 T (show (0 : ℝ≥0) ≤ T from zero_le)
        le_rfl (B n m) measurableSet_Ioc hSepNM)
  have hLpMP : MemLp (fun ω => (N m p ω).toReal - r m p) 2 P := by
    simpa only [N, r, B, tsub_zero] using
      (avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T p 0 T (show (0 : ℝ≥0) ≤ T from zero_le)
        le_rfl (B m p) measurableSet_Ioc hSepMP)
  have hCrossInt : Integrable (fun ω =>
      ((N n m ω).toReal - r n m) *
      ((N m p ω).toReal - r m p)) P := by
    exact MemLp.integrable_mul (p := 2) (q := 2) hLpNM hLpMP
  constructor
  · exact hCrossInt
  · have hExpand :
        (∫ ω, ((N n p ω).toReal - r n p) ^ 2 ∂P) =
        ∫ ω, (((N n m ω).toReal - r n m) ^ 2 +
          ((N m p ω).toReal - r m p) ^ 2) +
          2 * (((N n m ω).toReal - r n m) *
            ((N m p ω).toReal - r m p)) ∂P := by
        congr 1
        funext ω
        rw [hPhi ω]
        ring
    have hIntegrate :
        (∫ ω, (((N n m ω).toReal - r n m) ^ 2 +
          ((N m p ω).toReal - r m p) ^ 2) +
          2 * (((N n m ω).toReal - r n m) *
            ((N m p ω).toReal - r m p)) ∂P) =
        r n m + r m p +
          2 * (∫ ω, ((N n m ω).toReal - r n m) *
            ((N m p ω).toReal - r m p) ∂P) := by
        calc
          _ = (∫ ω, (((N n m ω).toReal - r n m) ^ 2 +
              ((N m p ω).toReal - r m p) ^ 2) ∂P) +
              (∫ ω, 2 * (((N n m ω).toReal - r n m) *
                ((N m p ω).toReal - r m p)) ∂P) := by
                  exact integral_add (hVNM.1.add hVMP.1)
                    (hCrossInt.const_mul (2 : ℝ))
          _ = (∫ ω, ((N n m ω).toReal - r n m) ^ 2 ∂P) +
              (∫ ω, ((N m p ω).toReal - r m p) ^ 2 ∂P) +
              2 * (∫ ω, ((N n m ω).toReal - r n m) *
                ((N m p ω).toReal - r m p) ∂P) := by
                  rw [integral_add hVNM.1 hVMP.1]
                  simp only [integral_const_mul, smul_eq_mul]
          _ = _ := by rw [hVNM.2, hVMP.2]
    have hFinal := hVNP.2
    rw [hExpand, hIntegrate, hRateAdd] at hFinal
    linarith
