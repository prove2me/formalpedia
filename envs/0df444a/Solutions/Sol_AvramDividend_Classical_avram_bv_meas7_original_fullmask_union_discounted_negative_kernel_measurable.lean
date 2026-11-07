-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_fullmask_union_discounted_negative_kernel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:02:07.228771+00:00
-- url     : https://prove2.me/submissions/765da76c-de6a-41c0-93bd-d52d1588f5d2

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_admissible_fullmask_predictable_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Joint marked stopped-kernel measurability for the exact original full-mask union. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) ∧
      ∀ S : ℝ≥0,
        let τ : Ω → ℝ≥0 := fun ω =>
          (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
        let Z : ℝ≥0 × Ω → ℝ := fun r =>
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          0 < Z p ∧ ENNReal.ofReal (Z p) < C}
        ((⋃ n : ℕ, {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Z p ∈ Icc (a n) (b n)}) = E) ∧
        Measurable[(𝓕.rightCont.predictable).prod
          (inferInstance : MeasurableSpace ℝ)]
          (fun p : (ℝ≥0 × Ω) × ℝ =>
            if p.1 ∈ E ∧ p.2 < 0 then
              Real.exp (-(q * (p.1.1 : ℝ))) *
                (w (Z p.1 + p.2) - w (Z p.1))
            else 0) := by
  obtain ⟨a, b, ha, ha2, hab, hBand, hEvent, hFull⟩ :=
    avram_bv_meas7_original_admissible_fullmask_predictable_exhaustion
      X x C hC D hD
  refine ⟨a, b, ha, ha2, hab, hBand, hEvent, ?_⟩
  intro S
  obtain ⟨hUnion, hE⟩ := hFull S
  refine ⟨hUnion, ?_⟩
  convert
    (avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
      X x D hD.1.1 w hw_cont hw_neg q _ hE) using 1
  funext p
  simp only [Set.mem_setOf_eq]
