-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_finite_NNReal_marked_times_pairwise_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:04:12.705985+00:00
-- url     : https://prove2.me/submissions/8cedbef2-b3b4-4e4e-84ca-9b8980bdb32b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

/-- Finite original marked-time sets have a positive minimum pairwise gap. -/
theorem solution
    (F : Finset ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ F, ∀ v ∈ F, u ≠ v →
        δ ≤ |(u : ℝ) - (v : ℝ)| := by
  classical
  let D : Finset ℝ :=
    ((F.product F).filter (fun q => q.1 ≠ q.2)).image
      (fun q => |(q.1 : ℝ) - (q.2 : ℝ)|)
  have hMem (u v : ℝ≥0) (hu : u ∈ F) (hv : v ∈ F) (hneq : u ≠ v) :
      |(u : ℝ) - (v : ℝ)| ∈ D := by
    apply Finset.mem_image.mpr
    refine ⟨(u, v), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hneq⟩
  have hDpos (d : ℝ) (hd : d ∈ D) : 0 < d := by
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hd
    have hneq : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
    have hcoe : (q.1 : ℝ) ≠ (q.2 : ℝ) := by exact_mod_cast hneq
    rw [← heq]
    exact abs_pos.mpr (sub_ne_zero.mpr hcoe)
  by_cases hD : D.Nonempty
  · refine ⟨D.min' hD, hDpos _ (Finset.min'_mem D hD), ?_⟩
    intro u hu v hv huv
    exact Finset.min'_le D _ (hMem u v hu hv huv)
  · refine ⟨1, by norm_num, ?_⟩
    intro u hu v hv huv
    exact False.elim (hD ⟨_, hMem u v hu hv huv⟩)
