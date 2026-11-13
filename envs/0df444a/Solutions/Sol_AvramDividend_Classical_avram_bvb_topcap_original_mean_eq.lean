-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:57:51.122277+00:00
-- url     : https://prove2.me/submissions/9b1dda80-031f-41cb-9c8b-3b4ce89cdf2b

import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_fullmask_predictable_prestate
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_marked_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_discounted_negative_kernel_product_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_finite_product_ae_bounded_kernel_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_stopped_L1_auto_source_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Campbell compensation of the literal original finite-activity full-mask jump sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hCapTop : C = ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    let V : ℕ → Ω → ℝ := fun n ω =>
      ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ n, (∫ ω, J n ω ∂P) = (∫ ω, V n ω ∂P) := by
  intro δ U H NX J V n
  letI : IsProbabilityMeasure P := X.isProbability
  let Tnn : ℝ≥0 := ⟨T, hT.le⟩
  let E : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
    (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧ 0 ≤ U p.1 p.2 ∧
    ENNReal.ofReal (U p.1 p.2) ≤ C}
  have hTime : Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω => p.1) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    apply measurable_of_Ioi
    intro a
    convert measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
      (i := a) (s := (Set.univ : Set Ω)) MeasurableSet.univ using 1
    ext p
    simp
  have hEm : MeasurableSet[𝓕.rightCont.predictable] E := by
    simpa only [E, U, δ] using (avram_bvb_topcap_original_fullmask_predictable_prestate X x D C hC hCapTop hD T hT n)
  obtain ⟨μ, hμ, hClock, hFubini⟩ := avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini X Tnn
  have hMeas : Measurable[(𝓕.rightCont.predictable).prod inferInstance] (H n) := by
    simpa only [H] using (avram_bvb_topcap_original_marked_predictable X hBV q hq w C hC hCapTop hw_cont hw_neg x D hD T hT hActivity n)
  have hKernel : (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable (H n) (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    obtain ⟨Kbound, hK0, hK⟩ := avram_bvb_topcap_original_discounted_negative_kernel_product_ae_bound
        X hBV q hq w C hC hCapTop hw_cont hw_neg x D hD
        T hT hActivity μ hμ hClock
    exact avram_bvb_topcap_finite_product_ae_bounded_kernel_integrable
      μ (X.ν.restrict (Iio (0 : ℝ))) hμ (by simpa using hActivity) (H n)
      hMeas.aestronglyMeasurable Kbound hK0 (hK n)
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let K : Ω → Measure ((ℝ≥0 × Ω) × ℝ) := fun ω => (NX ω).map
    (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
  let M : Measure ((ℝ≥0 × Ω) × ℝ) := P.bind K
  let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ Tnn}
  have hS : MeasurableSet S := measurableSet_le (hTime.comp measurable_fst) measurable_const
  let MT : Measure ((ℝ≥0 × Ω) × ℝ) := M.restrict S
  let N : Measure ((ℝ≥0 × Ω) × ℝ) := μ.prod (X.ν.restrict (Iio (0 : ℝ)))
  let B : ℕ → Set ℝ := fun _ => Set.univ
  have hSupport : S.indicator (H n) = H n := by
    funext p
    by_cases hp : p.1.1 ≤ Tnn
    · simp [S, hp]
    · have hle : T < (p.1.1 : ℝ) := by
        exact_mod_cast (lt_of_not_ge hp : Tnn < p.1.1)
      have hδ : 0 ≤ δ n := div_nonneg hT.le (by positivity)
      have hNotCut : ¬ (p.1.1 : ℝ) < T - δ n := by linarith
      simp [S, hp, H, hNotCut]
  have hSource := avram_p2_e_compensator_original_stopped_L1_auto_source_kernel
      X NX (by intro ω; rfl) K (by intro ω; rfl) M rfl Tnn S rfl hS MT N rfl
      μ hμ hClock rfl B
      (by intro k; exact MeasurableSet.univ)
      (by intro i j hij; exact Set.Subset.rfl)
      (by ext z; simp [B])
      (by intro k; simpa [B] using hActivity)
      (fun _ => ⊤) (by intro t; simp)
      (H n) hMeas hKernel (H n) (by funext p; simp) hSupport
  have hExpected : (∫ ω, J n ω ∂P) = (∫ p, H n p ∂N) := by
    simpa only [J] using sub_eq_zero.mp (hSource.2.2.2.2)
  have hClockMean := (hFubini (H n) hMeas hKernel).2
  have hTnn : (Tnn : ℝ) = T := rfl
  rw [hTnn] at hClockMean
  calc
    ∫ ω, J n ω ∂P = ∫ p, H n p ∂N := hExpected
    _ = ∫ ω, V n ω ∂P := by
      simpa only [V, N] using hClockMean.symm
