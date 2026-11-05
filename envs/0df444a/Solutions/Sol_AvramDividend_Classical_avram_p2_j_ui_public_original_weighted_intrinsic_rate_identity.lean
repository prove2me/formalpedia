-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_public_original_weighted_intrinsic_rate_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:51:27.807799+00:00
-- url     : https://prove2.me/submissions/3581061c-8837-4168-b4e4-13e705b38d11

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Weighted original intrinsic marked jump expectations equal time times intrinsic mark intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ markRate : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * markRate B) ∧
      (∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (Set.univ : Set ℝ)),
        g p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
        (T : ℝ≥0∞) * (∫⁻ y, g y ∂markRate) := by
  let C : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ (Set.univ : Set ℝ)
  have hC : MeasurableSet C := measurableSet_Ioc.prod MeasurableSet.univ
  let G : (ℝ≥0 × ℝ) → ℝ≥0∞ := C.indicator (fun p => g p.2)
  have hG : Measurable G := (hg.comp measurable_snd).indicator hC
  obtain ⟨Q, hQ, hWeighted⟩ :=
    avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini X G hG
  obtain ⟨markRate, hRate, _, _, _⟩ :=
    avram_p2_c_borel_original_intrinsic_intensity_measure_complete X
  let ρ : Measure ℝ := (Q.restrict C).map Prod.snd
  have hρ : ρ = (T : ℝ≥0∞) • markRate := by
    refine Measure.ext ?_
    intro B hB
    have hpre : MeasurableSet ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) :=
      measurable_snd hB
    have hset : ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩ C =
        Ioc 0 T ×ˢ B := by
      ext p
      simp [C]
      tauto
    calc
      ρ B = (Q.restrict C) ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) :=
        Measure.map_apply measurable_snd hB
      _ = Q (((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩ C) :=
        Measure.restrict_apply hpre
      _ = Q (Ioc 0 T ×ˢ B) := by rw [hset]
      _ = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P) := hQ _ (measurableSet_Ioc.prod hB)
      _ = (T : ℝ≥0∞) * markRate B := hRate T B hB
      _ = ((T : ℝ≥0∞) • markRate) B := by
        rw [Measure.smul_apply, smul_eq_mul]
  have hScale : (∫⁻ p in C, g p.2 ∂Q) =
      (T : ℝ≥0∞) * (∫⁻ y, g y ∂markRate) := by
    calc
      (∫⁻ p in C, g p.2 ∂Q) = (∫⁻ y, g y ∂ρ) := by
        exact (lintegral_map hg measurable_snd).symm
      _ = (∫⁻ y, g y ∂((T : ℝ≥0∞) • markRate)) := by rw [hρ]
      _ = (T : ℝ≥0∞) * (∫⁻ y, g y ∂markRate) := by
        rw [lintegral_smul_measure]
        simp only [smul_eq_mul]
  refine ⟨markRate, hRate T, ?_⟩
  calc
    (∫⁻ ω, ∫⁻ p in C,
      g p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
      (∫⁻ ω, ∫⁻ p, G p ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := by
          dsimp [G]
          simp_rw [lintegral_indicator hC]
    _ = (∫⁻ p, G p ∂Q) := hWeighted.symm
    _ = (∫⁻ p in C, g p.2 ∂Q) := by
      dsimp [G]
      rw [lintegral_indicator hC]
    _ = (T : ℝ≥0∞) * (∫⁻ y, g y ∂markRate) := hScale
