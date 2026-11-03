-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_predictable_discount_thinned_L2_tail_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:30:14.707529+00:00
-- url     : https://prove2.me/submissions/ea504911-8dfb-4a13-93dc-df80c6f0c9d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Predictably discounted square-energy tails of the original, ruin-stopped
negative-jump Taylor source vanish under arbitrary predictable mark thinning. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ 1)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let A : ℕ → Set ((ℝ≥0 × Ω) × ℝ) := fun n => {p | p.2 ∈ B n}
    Tendsto (fun n : ℕ =>
      ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        (A n).indicator (fun r =>
          ENNReal.ofReal ((a r.1 * (S.indicator HS r)) ^ 2)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by
  classical
  intro Y H HS A
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  let νneg := X.ν.restrict (Iio (0 : ℝ))
  let M := μ.prod νneg
  let F : ((ℝ≥0 × Ω) × ℝ) → ENNReal :=
    fun p => ENNReal.ofReal ((a p.1 * (S.indicator HS p)) ^ 2)
  have hEnergy :=
    avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ S hS a ham ha
  have hFMeas : Measurable F := by
    exact ENNReal.measurable_ofReal.comp (hEnergy.1.pow_const 2)
  have hAF (n : ℕ) : MeasurableSet (A n) :=
    (hBm n).preimage measurable_snd
  have hFn (n : ℕ) :
      AEMeasurable ((A n).indicator F) M :=
    (hFMeas.indicator (hAF n)).aemeasurable
  have hFullFin : (∫⁻ p, F p ∂M) ≠ ⊤ := by
    have hProd : (∫⁻ p, F p ∂M) =
        ∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
          F (p,z) ∂X.ν ∂μ :=
      lintegral_prod F hFMeas.aemeasurable
    rw [hProd]
    exact ne_of_lt hEnergy.2.2
  have hMono (p : ((ℝ≥0 × Ω) × ℝ)) :
      Antitone (fun n => (A n).indicator F p) := by
    intro n m hnm
    by_cases hm : p ∈ A m
    · have hn : p ∈ A n := hBanti hnm hm
      simp only [Set.indicator_of_mem hm, Set.indicator_of_mem hn]
      exact le_refl _
    · by_cases hn : p ∈ A n
      · simp only [Set.indicator_of_notMem hm, Set.indicator_of_mem hn]
        exact bot_le
      · simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem hn]
        exact le_refl _
  have hToZero (p : ((ℝ≥0 × Ω) × ℝ)) :
      Tendsto (fun n => (A n).indicator F p) atTop (𝓝 0) := by
    have hnexists : ∃ n, p.2 ∉ B n := by
      by_contra h
      push_neg at h
      have hp : p.2 ∈ ⋂ n, B n := Set.mem_iInter.2 h
      simpa [hBempty] using hp
    obtain ⟨n, hn⟩ := hnexists
    have hev : ∀ᶠ m : ℕ in atTop, (A m).indicator F p = 0 := by
      filter_upwards [eventually_ge_atTop n] with m hnm
      have hm : p ∉ A m := by
        intro hp
        exact hn (hBanti hnm hp)
      simp only [Set.indicator_of_notMem hm]
    exact (tendsto_congr' hev).mpr tendsto_const_nhds
  have hFirstFin :
      (∫⁻ p, (A 0).indicator F p ∂M) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hFullFin))
    apply lintegral_mono
    intro p
    by_cases hp : p ∈ A 0
    · simp only [Set.indicator_of_mem hp]
      exact le_refl _
    · simp only [Set.indicator_of_notMem hp]
      exact bot_le
  have hlim := lintegral_tendsto_of_tendsto_of_antitone
    hFn (Filter.Eventually.of_forall hMono) hFirstFin
    (Filter.Eventually.of_forall hToZero)
  simpa only [lintegral_zero] using hlim