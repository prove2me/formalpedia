-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_public_original_mark_marginal_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:53:10.501091+00:00
-- url     : https://prove2.me/submissions/bd017349-77e6-4366-8dec-b1a329cec2c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original expected negative-mark measure has the Tonelli
identity for every nonnegative measurable mark test at the original clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ ρ : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∫⁻ y, g y ∂ρ) =
        (∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (Set.univ : Set ℝ)),
          g p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := by
  let C : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ (Set.univ : Set ℝ)
  have hC : MeasurableSet C := measurableSet_Ioc.prod MeasurableSet.univ
  let G : (ℝ≥0 × ℝ) → ℝ≥0∞ :=
    C.indicator (fun p => g p.2)
  have hG : Measurable G :=
    (hg.comp measurable_snd).indicator hC
  obtain ⟨M, hM, hMG⟩ :=
    avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini X G hG
  let ρ : Measure ℝ := (M.restrict C).map Prod.snd
  refine ⟨ρ, ?_, ?_⟩
  · intro B hB
    have hpre : MeasurableSet ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) :=
      measurable_snd hB
    have hset : ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩ C =
        Ioc 0 T ×ˢ B := by
      ext p
      simp [C]
      tauto
    calc
      ρ B = (M.restrict C) ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) := by
        exact Measure.map_apply measurable_snd hB
      _ = M (((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩ C) := by
        exact Measure.restrict_apply hpre
      _ = M (Ioc 0 T ×ˢ B) := by rw [hset]
      _ = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ B) ∂P) :=
        hM (Ioc 0 T ×ˢ B) (measurableSet_Ioc.prod hB)
  · have hmap :
        (∫⁻ y, g y ∂ρ) =
        (∫⁻ p, g p.2 ∂(M.restrict C)) := by
      change (∫⁻ y, g y ∂(M.restrict C).map Prod.snd) = _
      exact lintegral_map hg measurable_snd
    calc
      (∫⁻ y, g y ∂ρ) =
          (∫⁻ p, g p.2 ∂(M.restrict C)) := hmap
      _ = (∫⁻ p, G p ∂M) := by
        exact (lintegral_indicator hC (fun p => g p.2)).symm
      _ = (∫⁻ ω, ∫⁻ p, G p ∂((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := hMG
      _ = _ := by
        dsimp [G]
        simp_rw [lintegral_indicator hC]
        simpa only [C]
