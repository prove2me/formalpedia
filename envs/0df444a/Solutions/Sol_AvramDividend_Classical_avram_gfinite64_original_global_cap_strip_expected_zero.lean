-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite64_original_global_cap_strip_expected_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:17:29.060198+00:00
-- url     : https://prove2.me/submissions/9930f1da-5ed9-409f-a8ef-1df4086e5719

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_adapted_capped_reserve_strict_at_fixed_time_ae
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gfinite56_cap_fraction_cutoff_tendsto
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Fixed-time strictness at a global cap makes its shrinking upper strip
    negligible on the original probability-time product space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (hc : 0 < c)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0), riskProcess X x D s ω ≤ c)
    (n : ℕ) (hn : 0 < n) :
    Tendsto
      (fun j : ℕ => ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) (n : ℝ))
  letI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let Y : Ω × ℝ → ℝ := fun z => riskProcess X x D (Real.toNNReal z.2) z.1
  let b : ℕ → ℝ := fun j => c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hY : Measurable Y := by
    exact (avram_p3_g2_original_prepayment_riskProcess_joint_measurable
      X x D hD).comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hRev : Measurable (fun z : ℝ × Ω => Y (z.2, z.1)) :=
    hY.comp (measurable_snd.prodMk measurable_fst)
  have hBad : MeasurableSet {z : ℝ × Ω |
      z.1 ∈ Ioo (0 : ℝ) (n : ℝ) ∧ c ≤ Y (z.2, z.1)} := by
    exact (measurableSet_Ioo.preimage measurable_fst).inter
      (measurableSet_le measurable_const hRev)
  have hSlices : ∀ᵐ t ∂μ, ∀ᵐ ω ∂P,
      ¬ (t ∈ Ioo (0 : ℝ) (n : ℝ) ∧ c ≤ Y (ω, t)) := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) (n : ℝ)
    · have htpos : 0 < Real.toNNReal t := Real.toNNReal_pos.mpr ht.1
      filter_upwards
        [avram_wave4_04_ubv_adapted_capped_reserve_strict_at_fixed_time_ae
          X hBV x c D hD (Real.toNNReal t) htpos] with ω hω
      intro h
      exact (not_le_of_gt (hω (fun s _ => hCap ω s))) h.2
    · exact Filter.Eventually.of_forall (fun _ h => ht h.1)
  have hSwap : ∀ᵐ ω ∂P, ∀ᵐ t ∂μ,
      ¬ (t ∈ Ioo (0 : ℝ) (n : ℝ) ∧ c ≤ Y (ω, t)) :=
    (Measure.ae_ae_comm hBad.compl).mp hSlices
  have hStrict : ∀ᵐ z ∂P.prod μ, Y z < c := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hY measurable_const)).2
    filter_upwards [hSwap] with ω hω
    filter_upwards [hω, ae_restrict_mem measurableSet_Ioo] with t ht hti
    exact lt_of_not_ge (fun hn => ht ⟨hti, hn⟩)
  have hb : Tendsto b atTop (𝓝 c) := by
    simpa only [b] using avram_gfinite56_cap_fraction_cutoff_tendsto c
  let f : ℕ → Ω × ℝ → ℝ := fun j z => if b j < Y z then 1 else 0
  have hfmeas (j : ℕ) : AEStronglyMeasurable (f j) (P.prod μ) :=
    (Measurable.ite (measurableSet_lt measurable_const hY)
      measurable_const measurable_const).aestronglyMeasurable
  have hfbound (j : ℕ) : ∀ᵐ z ∂P.prod μ, ‖f j z‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro z
    simp only [f]
    split_ifs <;> norm_num
  have hflim : ∀ᵐ z ∂P.prod μ,
      Tendsto (fun j => f j z) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hStrict] with z hz
    have hevent : ∀ᶠ j in atTop, Y z < b j :=
      hb.eventually (isOpen_Ioi.mem_nhds hz)
    have hzero : (fun j => f j z) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      filter_upwards [hevent] with j hj
      simp [f, not_lt.mpr (le_of_lt hj)]
    exact (tendsto_congr' hzero).mpr tendsto_const_nhds
  have hdc : Tendsto (fun j => ∫ z, f j z ∂P.prod μ)
      atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_integral_of_dominated_convergence
      (fun _ : Ω × ℝ => (1 : ℝ)) hfmeas (integrable_const (1 : ℝ)) hfbound hflim using 1
    simp
  have hfint (j : ℕ) : Integrable (f j) (P.prod μ) :=
    (integrable_const (μ := P.prod μ) (1 : ℝ)).mono' (hfmeas j)
      (Filter.Eventually.of_forall (fun z => by simp [f]; split_ifs <;> norm_num))
  have hEq (j : ℕ) : (∫ z, f j z ∂P.prod μ) =
      (∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if b j < riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P) := by
    simpa only [f, Y, μ] using integral_prod (f j) (hfint j)
  convert hdc using 1
  funext j
  exact (hEq j).symm
