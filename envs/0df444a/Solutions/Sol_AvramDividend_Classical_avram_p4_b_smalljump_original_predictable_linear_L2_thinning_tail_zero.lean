-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:36:55.143465+00:00
-- url     : https://prove2.me/submissions/64471628-dba9-4073-8100-24c60a584752

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original predictable linear Lévy small-jump L2 energy vanishes under
any measurable decreasing mark thinning to the empty set. -/
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
    Tendsto (fun n : ℕ => (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
      ({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator (fun r : ((ℝ≥0 × Ω) × ℝ) => ENNReal.ofReal ((g r.1 * r.2)^2)) p
      ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) atTop (𝓝 0) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  have hνs : SFinite (X.ν.restrict (Ioo (-1 : ℝ) 0)) := by
    have hsub : Ioo (-1 : ℝ) 0 ⊆ Iio 0 := fun _ hz => hz.2
    have heq : X.ν.restrict (Ioo (-1 : ℝ) 0) =
        (X.ν.restrict (Iio (0 : ℝ))).restrict (Ioo (-1 : ℝ) 0) :=
      (Measure.restrict_restrict_of_subset hsub).symm
    rw [heq]
    infer_instance
  letI : SFinite (X.ν.restrict (Ioo (-1 : ℝ) 0)) := hνs
  let M := μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))
  let F : ((ℝ≥0 × Ω) × ℝ) → ENNReal :=
    fun r => ENNReal.ofReal ((g r.1 * r.2)^2)
  let A : ℕ → Set ((ℝ≥0 × Ω) × ℝ) := fun n => {r | r.2 ∈ B n}
  have hgMeas : Measurable (fun r : ((ℝ≥0 × Ω) × ℝ) =>
      g r.1 * r.2) := (hgm.comp measurable_fst).mul measurable_snd
  have hFMeas : Measurable F := ENNReal.measurable_ofReal.comp
    (hgMeas.pow_const 2)
  have hFullFin : (∫⁻ r, F r ∂M) ≠ ⊤ := by
    have hProd : (∫⁻ r, F r ∂M) =
        ∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Ioo (-1 : ℝ) 0,
          ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ :=
      lintegral_prod F hFMeas.aemeasurable
    rw [hProd]
    exact ne_of_lt
      (avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
        X μ g hgm hgL2 (Ioo (-1 : ℝ) 0)
        (finite_small_negative_jump_square_moment X.ν X.ν_integrable)).2
  have hAF (n : ℕ) : MeasurableSet (A n) :=
    (hBm n).preimage measurable_snd
  have hFn (n : ℕ) : AEMeasurable ((A n).indicator F) M :=
    (hFMeas.indicator (hAF n)).aemeasurable
  have hMono (r : ((ℝ≥0 × Ω) × ℝ)) :
      Antitone (fun n => (A n).indicator F r) := by
    intro n m hnm
    by_cases hm : r ∈ A m
    · have hn : r ∈ A n := hBanti hnm hm
      simp only [Set.indicator_of_mem hm, Set.indicator_of_mem hn]
      exact le_refl _
    · by_cases hn : r ∈ A n
      · simp only [Set.indicator_of_notMem hm, Set.indicator_of_mem hn]
        exact bot_le
      · simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem hn]
        exact le_refl _
  have hToZero (r : ((ℝ≥0 × Ω) × ℝ)) :
      Tendsto (fun n => (A n).indicator F r) atTop (𝓝 0) := by
    have hnexists : ∃ n, r.2 ∉ B n := by
      by_contra h
      push_neg at h
      have hp : r.2 ∈ ⋂ n, B n := Set.mem_iInter.2 h
      simpa [hBempty] using hp
    obtain ⟨n, hn⟩ := hnexists
    have hev : ∀ᶠ m : ℕ in atTop, (A m).indicator F r = 0 := by
      filter_upwards [eventually_ge_atTop n] with m hnm
      have hm : r ∉ A m := by
        intro hr
        exact hn (hBanti hnm hr)
      simp only [Set.indicator_of_notMem hm]
    exact (tendsto_congr' hev).mpr tendsto_const_nhds
  have hFirstFin :
      (∫⁻ r, (A 0).indicator F r ∂M) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hFullFin))
    apply lintegral_mono
    intro r
    by_cases hr : r ∈ A 0
    · simp only [Set.indicator_of_mem hr]
      exact le_refl _
    · simp only [Set.indicator_of_notMem hr]
      exact bot_le
  have hlim := lintegral_tendsto_of_tendsto_of_antitone
    hFn (Filter.Eventually.of_forall hMono) hFirstFin
    (Filter.Eventually.of_forall hToZero)
  simpa only [lintegral_zero] using hlim
