-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:35:25.624816+00:00
-- url     : https://prove2.me/submissions/092b6f4b-1212-4030-bd55-9ea1cafe6a3d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (f : (ℝ≥0 × ℝ) → ℝ) (hf : Measurable f)
    (hfin : Integrable f
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) :
    (∫ p, f p ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑' u : ℝ≥0, if 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
      then f (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      else 0 := by
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hj : Measurable j := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      (Measurable.prodMk measurable_id measurable_const)
  have hpos : MeasurableSet {u : ℝ≥0 | 0 < u} :=
    measurableSet_lt measurable_const measurable_id
  have hnonzero : MeasurableSet {u : ℝ≥0 | j u ≠ 0} :=
    (measurableSet_eq_fun hj measurable_const).compl
  have hS : MeasurableSet {u : ℝ≥0 | 0 < u ∧ j u ≠ 0} :=
    hpos.inter hnonzero
  have hF : Measurable (fun u : ℝ≥0 => (u, j u)) :=
    Measurable.prodMk measurable_id hj
  change (∫ p, f p ∂
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u)))) =
    ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then f (u, j u) else 0
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u))
  have hfinμ : Integrable f μ := by
    exact hfin
  have hnorm : (∫⁻ p, ‖f p‖ₑ ∂μ) < ⊤ :=
    hfinμ.hasFiniteIntegral
  have hposfin : (∫⁻ p, ENNReal.ofReal (f p) ∂μ) < ⊤ :=
    lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm f) hnorm
  have hnegfin : (∫⁻ p, ENNReal.ofReal (-f p) ∂μ) < ⊤ := by
    have hle := lintegral_ofReal_le_lintegral_enorm
      (fun p : ℝ≥0 × ℝ => -f p) (μ := μ)
    have hnegNorm : (∫⁻ p, ‖-f p‖ₑ ∂μ) < ⊤ := by
      simpa only [enorm_neg] using hnorm
    exact lt_of_le_of_lt hle hnegNorm
  let pfun : ℝ≥0 → ℝ≥0∞ := fun u =>
    if 0 < u ∧ j u ≠ 0 then ENNReal.ofReal (f (u, j u)) else 0
  let nfun : ℝ≥0 → ℝ≥0∞ := fun u =>
    if 0 < u ∧ j u ≠ 0 then ENNReal.ofReal (-f (u, j u)) else 0
  have hposeq : (∫⁻ p, ENNReal.ofReal (f p) ∂μ) = ∑' u, pfun u := by
    exact avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
      X ω (fun p => ENNReal.ofReal (f p))
      (ENNReal.measurable_ofReal.comp hf)
  have hnegeq : (∫⁻ p, ENNReal.ofReal (-f p) ∂μ) = ∑' u, nfun u := by
    exact avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
      X ω (fun p => ENNReal.ofReal (-f p))
      (ENNReal.measurable_ofReal.comp hf.neg)
  have hpsummable : Summable (fun u : ℝ≥0 => (pfun u).toReal) :=
    ENNReal.summable_toReal (by
      rw [← hposeq]
      exact ne_of_lt hposfin)
  have hnsummable : Summable (fun u : ℝ≥0 => (nfun u).toReal) :=
    ENNReal.summable_toReal (by
      rw [← hnegeq]
      exact ne_of_lt hnegfin)
  have hpterm : ∀ u : ℝ≥0, pfun u ≠ ⊤ := by
    intro u
    dsimp [pfun]
    split <;> simp
  have hnterm : ∀ u : ℝ≥0, nfun u ≠ ⊤ := by
    intro u
    dsimp [nfun]
    split <;> simp
  have hparts (x : ℝ) :
      (ENNReal.ofReal x).toReal -
        (ENNReal.ofReal (-x)).toReal = x := by
    rcases le_total 0 x with hx | hx
    · have hnegx : -x ≤ 0 := neg_nonpos.mpr hx
      simp [ENNReal.toReal_ofReal hx, ENNReal.ofReal_eq_zero.mpr hnegx]
    · have hposneg : 0 ≤ -x := neg_nonneg.mpr hx
      simp [ENNReal.ofReal_eq_zero.mpr hx, ENNReal.toReal_ofReal hposneg]
  change (∫ p, f p ∂μ) =
    ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then f (u, j u) else 0
  calc
    (∫ p, f p ∂μ) =
        (∫⁻ p, ENNReal.ofReal (f p) ∂μ).toReal -
          (∫⁻ p, ENNReal.ofReal (-f p) ∂μ).toReal :=
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfinμ
    _ = (∑' u : ℝ≥0, pfun u).toReal - (∑' u : ℝ≥0, nfun u).toReal := by
      rw [hposeq, hnegeq]
    _ = (∑' u : ℝ≥0, (pfun u).toReal) -
          (∑' u : ℝ≥0, (nfun u).toReal) := by
      rw [ENNReal.tsum_toReal_eq hpterm, ENNReal.tsum_toReal_eq hnterm]
    _ = (∑' u : ℝ≥0, ((pfun u).toReal - (nfun u).toReal)) := by
      rw [hpsummable.tsum_sub hnsummable]
    _ = (∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then f (u, j u) else 0) := by
      apply tsum_congr
      intro u
      by_cases hu : 0 < u ∧ j u ≠ 0
      · simp only [pfun, nfun, if_pos hu]
        exact hparts (f (u, j u))
      · simp [pfun, nfun, hu]
