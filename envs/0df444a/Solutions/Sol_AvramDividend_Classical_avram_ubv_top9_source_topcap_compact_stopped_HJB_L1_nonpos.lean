-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_source_topcap_compact_stopped_HJB_L1_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:10:17.279864+00:00
-- url     : https://prove2.me/submissions/7f1761d2-da2d-4395-9ef4-a5f1019df948

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_source_topcap_compact_generator_stopped_time_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original infinite-cap compact HJB drift has nonpositive stopped expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ a b B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (ha : 0 < a) (hau : a < u + δ) (hvb : v < b) (hb : b < B)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    Integrable (fun ω : Ω => ∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω : Ω, (∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
  let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
  have hL1 : Integrable (fun ω : Ω => ∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P :=
    avram_ubv_top9_source_topcap_compact_generator_stopped_time_L1
      X x D C hD hTop w hw_smooth hw_cont hw_neg q hw_gen hw_grad
      u v δ a b B hu hδ hδone huv hv ha hau hvb hb T σ hσstop
  have hR : ∀ p : ℝ≥0 × Ω, R p ≤ 0 := by
    intro p
    dsimp [R, ρ]
    by_cases hruin : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
    · simp only [if_pos hruin, one_mul]
      by_cases hband : Y p ∈ Icc (u + δ) v
      · simp only [if_pos hband]
        apply (hw_gen (Y p) ?_ ?_).2
        · have hbnd := (Set.mem_Icc.mp hband).1
          linarith
        · simp [hTop]
      · simp [hband]
    · simp [hruin]
  have hpath : ∀ ω : Ω,
      (∫ t : ℝ≥0,
        if t ≤ σ ω then R (t, ω) else 0
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) ≤ 0 := by
    intro ω
    apply MeasureTheory.integral_nonpos_of_ae
    filter_upwards [] with t
    split_ifs
    · exact hR (t, ω)
    · exact le_refl 0
  exact ⟨hL1, MeasureTheory.integral_nonpos_of_ae
    (Filter.Eventually.of_forall hpath)⟩
