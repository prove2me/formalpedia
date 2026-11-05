-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_four_strict_endpoints_jump_cell_C1_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:44:53.071889+00:00
-- url     : https://prove2.me/submissions/bd8120d8-44d8-4f4c-886b-a455544e20ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_h_localise_finite_interior_mesh_reserves_common_band
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_compact_C1_jump_cell_four_pairs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Strict original four-endpoint interior implies all physical jump-pair C1 bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) (hn : 0 < n) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    (∀ i, i < n →
      z i ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      z i + c i ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      z i - j i ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      z i + c i - j i ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) →
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i, i < n →
      (|w (z i + c i - j i) - w (z i - j i)| ≤ L * |c i|) ∧
      (|w (z i + c i) - w (z i)| ≤ L * |c i|) ∧
      (|w (z i + c i - j i) - w (z i + c i)| ≤ L * |j i|) ∧
      (|w (z i - j i) - w (z i)| ≤ L * |j i|) := by
  intro J Y z c j hInside
  let A : Finset ℝ := (Finset.range n).image z
  let B : Finset ℝ := (Finset.range n).image (fun i => z i + c i)
  let E : Finset ℝ := (Finset.range n).image (fun i => z i - j i)
  let F : Finset ℝ := (Finset.range n).image (fun i => z i + c i - j i)
  let S : Finset ℝ := (A ∪ B) ∪ (E ∪ F)
  have hS : S.Nonempty := by
    have hZero : z 0 ∈ A := Finset.mem_image.mpr
      ⟨0, Finset.mem_range.mpr hn, rfl⟩
    exact ⟨z 0, Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl hZero)))⟩
  have hSInside : ∀ v ∈ S, 0 < v ∧ ENNReal.ofReal v < C := by
    intro v hv
    rcases Finset.mem_union.mp hv with hAB | hEF
    · rcases Finset.mem_union.mp hAB with hA | hB
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
        exact (hInside i (Finset.mem_range.mp hi)).1
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
        exact (hInside i (Finset.mem_range.mp hi)).2.1
    · rcases Finset.mem_union.mp hEF with hE | hF
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hE
        exact (hInside i (Finset.mem_range.mp hi)).2.2.1
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hF
        exact (hInside i (Finset.mem_range.mp hi)).2.2.2
  obtain ⟨a, b, ha, ha2, hab, hContain, hBand⟩ :=
    avram_p3_h_localise_finite_interior_mesh_reserves_common_band
      C S hS hSInside
  have hAll : ∀ v ∈ S, v ∈ Set.Icc (a / 2) b := by
    intro v hv
    have h := hContain v hv
    exact ⟨by linarith [h.1], h.2⟩
  have hPts : ∀ i, i < n →
      z i ∈ Set.Icc (a / 2) b ∧
      z i + c i ∈ Set.Icc (a / 2) b ∧
      z i - j i ∈ Set.Icc (a / 2) b ∧
      z i + c i - j i ∈ Set.Icc (a / 2) b := by
    intro i hi
    have hiR : i ∈ Finset.range n := Finset.mem_range.mpr hi
    have hA : z i ∈ A := Finset.mem_image.mpr ⟨i, hiR, rfl⟩
    have hB : z i + c i ∈ B := Finset.mem_image.mpr ⟨i, hiR, rfl⟩
    have hE : z i - j i ∈ E := Finset.mem_image.mpr ⟨i, hiR, rfl⟩
    have hF : z i + c i - j i ∈ F := Finset.mem_image.mpr ⟨i, hiR, rfl⟩
    refine ⟨hAll _ (Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl hA)))), ?_, ?_, ?_⟩
    · exact hAll _ (Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr hB))))
    · exact hAll _ (Finset.mem_union.mpr
        (Or.inr (Finset.mem_union.mpr (Or.inl hE))))
    · exact hAll _ (Finset.mem_union.mpr
        (Or.inr (Finset.mem_union.mpr (Or.inr hF))))
  exact avram_p3_f2_original_stopped_compact_C1_jump_cell_four_pairs
    X x C D hD w hwC1 a b (by linarith) hBand ω u n hPts
