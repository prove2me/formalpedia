-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_original_annulus_past_future_borel_covariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:32:26.044708+00:00
-- url     : https://prove2.me/submissions/3ba9877d-6101-4206-8849-ced67e20f2a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_nested_cutoff_annulus_count_additive
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_offtime_borel_count_integrable_zero_covariance
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- The physical annulus is the centred difference of two original cutoff counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) (hnm : n ≤ m)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((m : ℝ) + 1)))) :
    let K : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((i : ℝ) + 1))))
    let A : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))))
    let F : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℕ → ℝ := fun i =>
      ((s : ℝ≥0∞) * X.ν (Iic (-(1 / ((i : ℝ) + 1))))).toReal
    let q : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((A ω).toReal - (r m - r n)) *
      ((F ω).toReal - q)) P ∧
    (∫ ω, ((A ω).toReal - (r m - r n)) *
      ((F ω).toReal - q) ∂P) = 0 := by
  let K : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 s ×ˢ Iic (-(1 / ((i : ℝ) + 1))))
  let A : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 s ×ˢ Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))))
  let F : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let r : ℕ → ℝ := fun i =>
    ((s : ℝ≥0∞) * X.ν (Iic (-(1 / ((i : ℝ) + 1))))).toReal
  let q : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => ((A ω).toReal - (r m - r n)) *
      ((F ω).toReal - q)) P ∧
    (∫ ω, ((A ω).toReal - (r m - r n)) *
      ((F ω).toReal - q) ∂P) = 0
  have hCm :=
    avram_p4_f3_original_offtime_borel_count_integrable_zero_covariance
      X s t hst m m ε hε B hB hBand hCut
  change Integrable (fun ω => ((K m ω).toReal - r m) *
      ((F ω).toReal - q)) P ∧
    (∫ ω, ((K m ω).toReal - r m) * ((F ω).toReal - q) ∂P) = 0 at hCm
  have hCn :=
    avram_p4_f3_original_offtime_borel_count_integrable_zero_covariance
      X s t hst n m ε hε B hB hBand hCut
  change Integrable (fun ω => ((K n ω).toReal - r n) *
      ((F ω).toReal - q)) P ∧
    (∫ ω, ((K n ω).toReal - r n) * ((F ω).toReal - q) ∂P) = 0 at hCn
  have hFin (i : ℕ) (ω : Ω) : K i ω ≠ ⊤ := by
    have hCard :=
      (avram_p4_f_assembly_original_negative_band_factorial_pair_identity
        X ω s i).1
    change K i ω =
      (((avram_wave7_06_original_negative_band_marked_times_finite
        X ω s i).toFinset).card : ℝ≥0∞) at hCard
    rw [hCard]
    simp
  have hAReal (ω : Ω) :
      (A ω).toReal = (K m ω).toReal - (K n ω).toReal := by
    have hSplit :=
      avram_mixed_source13_original_nested_cutoff_annulus_count_additive
        X s n m hnm ω
    change K m ω = K n ω + A ω at hSplit
    have hANe : A ω ≠ ⊤ := by
      intro htop
      have hBad : K m ω = ⊤ := by simpa [htop] using hSplit
      exact (hFin m ω) hBad
    have hReal := congrArg ENNReal.toReal hSplit
    rw [ENNReal.toReal_add (hFin n ω) hANe] at hReal
    linarith
  have hFun :
      (fun ω => ((A ω).toReal - (r m - r n)) *
        ((F ω).toReal - q)) =
      (fun ω => ((K m ω).toReal - r m) * ((F ω).toReal - q) -
        ((K n ω).toReal - r n) * ((F ω).toReal - q)) := by
    funext ω
    rw [hAReal ω]
    ring
  constructor
  · rw [hFun]
    exact hCm.1.sub hCn.1
  · rw [hFun, integral_sub hCm.1 hCn.1, hCm.2, hCn.2]
    ring
