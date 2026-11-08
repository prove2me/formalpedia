-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_compact_stopped_compensated_jump_HJB_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:18:34.997703+00:00
-- url     : https://prove2.me/submissions/f5267d94-280e-4074-abe9-56e96628441c

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_finitecap_real_interior_HJB_bridge
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_discounted_compact_B_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_stopped_compensated_Taylor_plus_HJB_drift_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original compensated Taylor jump martingale plus the source-exact
compact HJB generator drift has nonpositive stopped expectation under a finite cap.
The physical right-payment reserve, Lévy jump measure and ruin guard are retained. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C.toReal)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    let Y0 : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let E : Set (ℝ≥0 × Ω) := {p | Y0 p ∈ Icc (u + δ) v}
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    let M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)) := P.bind K
    let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
    let MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)) := M.restrict S
    ∀ (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))),
      let a : (ℝ≥0 × Ω) → ℝ := fun p =>
        if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
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
      let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
      let GWσ : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1.1 ≤ σ p.1.2 then GW p else 0
      let B : Ω → ℝ := fun ω =>
        ∫ t : ℝ≥0,
          (if (t, ω) ∈ E then
            (if t ≤ T then Real.exp (-(q * (t : ℝ))) else 0) *
              (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) *
              (X.generator w (Y (t, ω)) - q * w (Y (t, ω)))
           else 0)
          ∂(((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal)
      Integrable (fun ω =>
        ((∫ p, GWσ ((p.1, ω), p.2) ∂(NX ω)) -
         (∫ t, ∫ z, GWσ ((t, ω), z)
            ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal))) + B ω) P ∧
      (∫ ω,
        ((∫ p, GWσ ((p.1, ω), p.2) ∂(NX ω)) -
         (∫ t, ∫ z, GWσ ((t, ω), z)
            ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal))) + B ω ∂P) ≤ 0  := by
  classical
  let Y0 : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let E : Set (ℝ≥0 × Ω) := {p | Y0 p ∈ Icc (u + δ) v}
  have hwReal : ContDiffOn ℝ 2 w (Ioo 0 C.toReal) :=
    (avram_ubv_loc6_finitecap_real_interior_HJB_bridge
      X w C hC hFinite hw_smooth q hw_gen hw_grad).1
  have hE : ∀ p ∈ E,
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      0 < y ∧ ENNReal.ofReal y < C := by
    intro p hp
    dsimp only
    change Y0 p ∈ Icc (u + δ) v at hp
    have hpos : 0 < Y0 p := by
      have hbound : u + δ ≤ Y0 p := hp.1
      linarith
    refine ⟨hpos, ?_⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hpos) hFinite).2
      (lt_of_le_of_lt hp.2 hv)
  have hB := avram_ubv_finite9_original_discounted_compact_B_L1
    X x D C hD hC hFinite w hw_smooth hw_cont hw_neg q hq
    hw_gen hw_grad u v δ hu hδ hδone huv hv T
  have hJump := avram_ubv_ito_jumps14_original_stopped_compensated_Taylor_plus_HJB_drift_nonpos
    X x D hD.1.1 w C.toReal u v δ hwReal hw_cont hw_neg
    hu hδ hδone huv hv q hq T C hw_gen E hE
  dsimp only at hB hJump ⊢
  intro σ hσ
  have hResult := hJump σ hσ (by
    convert hB using 1
    funext ω
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases hlo : u + δ ≤ Y0 (t, ω)
    · by_cases hhi : Y0 (t, ω) ≤ v
      · simp [E, Y0, mem_Icc, hlo, hhi, mul_assoc]
      · simp [E, Y0, mem_Icc, hlo, hhi]
    · simp [E, Y0, mem_Icc, hlo])
  simpa [E, Y0] using hResult
