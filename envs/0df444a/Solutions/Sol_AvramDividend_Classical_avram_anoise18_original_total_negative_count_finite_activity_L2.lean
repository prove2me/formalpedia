-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise18_original_total_negative_count_finite_activity_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:57:21.386197+00:00
-- url     : https://prove2.me/submissions/044c1592-da5f-4525-803c-76ef6c5e59b4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_uniform_count_L2
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_negative_cutoff_counts_monotone_exhaust
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical finite-activity all-negative count has a quadratic rate bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
    let R : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    Integrable (fun ω => (N ω).toReal ^ 2) P ∧
      (∫ ω, (N ω).toReal ^ 2 ∂P) ≤ R ^ 2 + R := by
  intro N R
  let Ncut : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  let C : ℝ := R ^ 2 + R
  have hCount (ω : Ω) :
      Monotone (fun n : ℕ => Ncut n ω) ∧
        N ω = ⨆ n : ℕ, Ncut n ω := by
    simpa only [N, Ncut] using
      avram_anoise18_original_negative_cutoff_counts_monotone_exhaust X T ω
  have hMom (n : ℕ) :
      Integrable (fun ω => (Ncut n ω).toReal ^ 2) P ∧
      (∫ ω, (Ncut n ω).toReal ^ 2 ∂P) ≤ C := by
    simpa only [Ncut, R, C] using
      avram_ubv_mixed13_original_finite_activity_uniform_count_L2 X hFinite T n
  have hMeasCut (n : ℕ) : Measurable (Ncut n) := by
    simpa only [Ncut] using
      avram_p2_e_compensator_original_intrinsic_marked_count_measurable
        X 0 T (by exact zero_le)
        (Iic (-(1 / ((n : ℝ) + 1)))) measurableSet_Iic
  have hMeasAll : Measurable N := by
    simpa only [N] using
      avram_p2_e_compensator_original_intrinsic_marked_count_measurable
        X 0 T (by exact zero_le) (Iio (0 : ℝ)) measurableSet_Iio
  have hFin : ∀ᵐ ω ∂P, N ω < ⊤ := by
    filter_upwards [
      avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
        X hFinite] with ω hω
    simpa only [N] using hω T
  have hCutFin : ∀ᵐ ω ∂P, ∀ n : ℕ, Ncut n ω ≠ ⊤ := by
    filter_upwards [hFin] with ω hω
    intro n
    have hle : Ncut n ω ≤ N ω := by
      rw [(hCount ω).2]
      exact le_iSup (fun k : ℕ => Ncut k ω) n
    exact ne_of_lt (lt_of_le_of_lt hle hω)
  have hCutReal (n : ℕ) :
      ∀ᵐ ω ∂P,
        Ncut n ω ^ 2 =
          ENNReal.ofReal ((Ncut n ω).toReal ^ 2) := by
    filter_upwards [hCutFin] with ω hω
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg 2,
        ENNReal.ofReal_toReal (hω n)]
  have hAllReal :
      ∀ᵐ ω ∂P, N ω ^ 2 = ENNReal.ofReal ((N ω).toReal ^ 2) := by
    filter_upwards [hFin] with ω hω
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg 2,
        ENNReal.ofReal_toReal (ne_of_lt hω)]
  have hCutL (n : ℕ) :
      (∫⁻ ω, Ncut n ω ^ 2 ∂P) ≤ ENNReal.ofReal C := by
    calc
      (∫⁻ ω, Ncut n ω ^ 2 ∂P) =
          ∫⁻ ω, ENNReal.ofReal ((Ncut n ω).toReal ^ 2) ∂P :=
        lintegral_congr_ae (hCutReal n)
      _ = ENNReal.ofReal
          (∫ ω, (Ncut n ω).toReal ^ 2 ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal (hMom n).1
          (Filter.Eventually.of_forall (fun ω => sq_nonneg _))).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hMom n).2
  have hMonSq :
      Monotone (fun n : ℕ => fun ω : Ω => Ncut n ω ^ 2) := by
    intro n m hnm ω
    simpa only [pow_two] using
      (mul_self_le_mul_self (show 0 ≤ Ncut n ω from bot_le)
        ((hCount ω).1 hnm))
  have hSupSq (ω : Ω) :
      N ω ^ 2 = ⨆ n : ℕ, Ncut n ω ^ 2 := by
    rw [(hCount ω).2, ENNReal.iSup_pow]
  have hAllL :
      (∫⁻ ω, N ω ^ 2 ∂P) ≤ ENNReal.ofReal C := by
    calc
      (∫⁻ ω, N ω ^ 2 ∂P) =
          ∫⁻ ω, ⨆ n : ℕ, Ncut n ω ^ 2 ∂P := by
            apply lintegral_congr
            intro ω
            exact hSupSq ω
      _ = ⨆ n : ℕ, (∫⁻ ω, Ncut n ω ^ 2 ∂P) :=
        lintegral_iSup (fun n => (hMeasCut n).pow_const 2) hMonSq
      _ ≤ ENNReal.ofReal C := iSup_le hCutL
  have hRealMeas :
      AEStronglyMeasurable (fun ω => (N ω).toReal ^ 2) P :=
    ((ENNReal.measurable_toReal.comp hMeasAll).pow_const 2).aestronglyMeasurable
  have hNonneg : 0 ≤ᵐ[P] (fun ω => (N ω).toReal ^ 2) :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hRealL :
      (∫⁻ ω, ENNReal.ofReal ((N ω).toReal ^ 2) ∂P) ≤
        ENNReal.ofReal C := by
    calc
      (∫⁻ ω, ENNReal.ofReal ((N ω).toReal ^ 2) ∂P) =
          ∫⁻ ω, N ω ^ 2 ∂P :=
        lintegral_congr_ae (hAllReal.mono (fun _ h => h.symm))
      _ ≤ ENNReal.ofReal C := hAllL
  have hRealLfinite :
      (∫⁻ ω, ENNReal.ofReal ((N ω).toReal ^ 2) ∂P) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hRealL
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  have hInt : Integrable (fun ω => (N ω).toReal ^ 2) P :=
    (lintegral_ofReal_ne_top_iff_integrable hRealMeas hNonneg).mp hRealLfinite
  have hC : 0 ≤ C := by
    dsimp [C, R]
    positivity
  refine ⟨hInt, ?_⟩
  change (∫ ω, (N ω).toReal ^ 2 ∂P) ≤ C
  calc
    (∫ ω, (N ω).toReal ^ 2 ∂P) =
        (∫⁻ ω, ENNReal.ofReal ((N ω).toReal ^ 2) ∂P).toReal :=
      integral_eq_lintegral_of_nonneg_ae hNonneg hRealMeas
    _ ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hRealL
    _ = C := ENNReal.toReal_ofReal hC