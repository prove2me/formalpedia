-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_source_topcap_discounted_stopped_HJB_L1_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:18:25.905686+00:00
-- url     : https://prove2.me/submissions/c96eae5a-7e61-4997-8606-d52407db32ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_source_topcap_discounted_compact_stopped_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original infinite-cap discounted compact HJB drift is L1 and has nonpositive expectation. -/
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
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u v δ B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (ρ p * (if Y p ∈ Icc (u + δ) v then
          X.generator w (Y p) - q * w (Y p) else 0))
    Integrable (fun ω => ∫ t : ℝ≥0,
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
    Real.exp (-(q * (p.1 : ℝ))) *
      (ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0))
  have hL1 : Integrable (fun ω => ∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P :=
    avram_ubv_top9_source_topcap_discounted_compact_stopped_L1
      X x D C hD hTop w hw_smooth hw_cont hw_neg q hq hw_gen
      u v δ B hu hδ hδone huv hv T σ hσstop
  have hR : ∀ p : ℝ≥0 × Ω, R p ≤ 0 := by
    intro p
    dsimp [R, ρ]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
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
    exact Filter.Eventually.of_forall (fun t => by
      by_cases ht : t ≤ σ ω
      · simpa [ht] using hR (t, ω)
      · simp [ht])
  exact ⟨hL1, MeasureTheory.integral_nonpos_of_ae
    (Filter.Eventually.of_forall hpath)⟩
