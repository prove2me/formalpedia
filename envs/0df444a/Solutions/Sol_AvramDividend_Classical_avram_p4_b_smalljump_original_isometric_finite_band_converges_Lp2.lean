-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_isometric_finite_band_converges_Lp2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:24:06.276945+00:00
-- url     : https://prove2.me/submissions/8f30a322-fcb2-43e5-9a9d-f4860a54f966

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_linear_isometry_cutoff_Lp2_error
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under an explicit original compensated source isometry, the finite
negative-mark truncations of every predictable linear jump kernel converge
in L2(P) to its full small-jump integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => g p.1 * p.2;
      let hML : MemLp G (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) :=
        avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
          X μ g hgm hgL2;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ v, ‖I v‖ = ‖v‖),
      Tendsto (fun n : ℕ =>
        let A : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.2 ∉ B n}
        I ((hML.indicator ((hBm n).preimage measurable_snd).compl).toLp
          (A.indicator G))) atTop (𝓝 (I (hML.toLp G)))) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro G hML I hIso
  let M : Measure ((ℝ≥0 × Ω) × ℝ) := μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))
  let A : ℕ → Set ((ℝ≥0 × Ω) × ℝ) := fun n => {p | p.2 ∉ B n}
  have hA (n : ℕ) : MeasurableSet (A n) :=
    ((hBm n).preimage measurable_snd).compl
  have hAc (n : ℕ) :
      (A n)ᶜ = {p : ((ℝ≥0 × Ω) × ℝ) | p.2 ∈ B n} := by
    ext p
    simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  have hErr (n : ℕ) :
      ‖I ((hML.indicator (hA n)).toLp ((A n).indicator G)) -
          I (hML.toLp G)‖ ≤
        (eLpNorm ((A n)ᶜ.indicator G) (2 : ℝ≥0∞) M).toReal := by
    exact avram_p4_b_smalljump_original_linear_isometry_cutoff_Lp2_error
      X μ g hgm hgL2 (A n) (hA n) I hIso
  have hTail : Tendsto (fun n : ℕ =>
      eLpNorm ((A n)ᶜ.indicator G) (2 : ℝ≥0∞) M) atTop (𝓝 0) := by
    convert avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
      X μ g hgm hgL2 B hBm hBanti hBempty using 1
    funext n
    rw [hAc n]
  have hFin (n : ℕ) :
      eLpNorm ((A n)ᶜ.indicator G) (2 : ℝ≥0∞) M ≠ ⊤ :=
    ne_of_lt (hML.indicator (hA n).compl).eLpNorm_lt_top
  have hTailR : Tendsto (fun n : ℕ =>
      (eLpNorm ((A n)ᶜ.indicator G) (2 : ℝ≥0∞) M).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff hFin).2 hTail
  have hNorm : Tendsto (fun n : ℕ =>
      ‖I ((hML.indicator (hA n)).toLp ((A n).indicator G)) -
        I (hML.toLp G)‖) atTop (𝓝 0) :=
    Filter.Tendsto.squeeze' tendsto_const_nhds hTailR
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (Filter.Eventually.of_forall hErr)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hNorm
