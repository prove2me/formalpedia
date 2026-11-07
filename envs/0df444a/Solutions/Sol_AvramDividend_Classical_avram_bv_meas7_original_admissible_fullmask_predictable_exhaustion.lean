-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_admissible_fullmask_predictable_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:23:14.516371+00:00
-- url     : https://prove2.me/submissions/3d391850-935c-49b8-b28f-e2b9dd849948

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_full_predictable_compact_bands
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_stopped_fullmask_union_of_cofinal_bands
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real full-band exhaustion and predictability for the original
ruin-stopped dividend-controlled left-limit process at every finite clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
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
        let Z : ℝ≥0 × Ω → ℝ := fun p =>
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
        ((⋃ n : ℕ, {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Z p ∈ Icc (a n) (b n)}) =
          {p : ℝ≥0 × Ω |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            0 < Z p ∧ ENNReal.ofReal (Z p) < C}) ∧
        MeasurableSet[𝓕.rightCont.predictable]
          {p : ℝ≥0 × Ω |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            0 < Z p ∧ ENNReal.ofReal (Z p) < C} := by
  obtain ⟨a, b, ha, ha2, hab, hBand, hEvent⟩ :=
    avram_bv_meas7_allcap_full_predictable_compact_bands C hC
  refine ⟨a, b, ha, ha2, hab, hBand, hEvent, ?_⟩
  intro S
  constructor
  · exact avram_bv_meas7_original_stopped_fullmask_union_of_cofinal_bands
      X x C D a b ha hBand hEvent S
  · exact (avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable
      X x C D hD S).2.2.1
