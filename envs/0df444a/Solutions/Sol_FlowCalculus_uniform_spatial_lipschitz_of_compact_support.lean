-- Prove2me | solution 1 for FlowCalculus.uniform_spatial_lipschitz_of_compact_support
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T19:24:03.711234+00:00
-- url     : https://prove2.me/submissions/58953639-2556-40e2-95b4-54c9650fbe2e

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Congr

open Set
open scoped ContDiff Topology NNReal

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (a b : ℝ) : ∃ L : ℝ≥0, ∀ t ∈ Icc a b, LipschitzWith L (X t) := by
  have hDb : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ y, ‖fderiv ℝ (X t) y‖ ≤ B := by
    obtain ⟨K, hK, hz⟩ := hsupp
    have hD : ContDiff ℝ ∞ (fun p : ℝ × V => fderiv ℝ (X p.1) p.2) := by
      have hh : ContDiff ℝ ∞ (fun p : (ℝ × V) × V => X p.1.1 p.2) :=
        hX.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact hh.fderiv contDiff_snd (by simp)
    have hzero : ∀ t y, y ∉ K → fderiv ℝ (X t) y = 0 := by
      intro t y hy
      have heq : X t =ᶠ[𝓝 y] (fun _ : V => (0 : V)) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hy] with z hzK
        exact hz t z hzK
      simpa using heq.fderiv_eq (𝕜 := ℝ)
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).bddAbove_image hD.continuous.norm.continuousOn
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro t ht y
    by_cases hy : y ∈ K
    · exact (hB (mem_image_of_mem (fun p : ℝ × V => ‖fderiv ℝ (X p.1) p.2‖)
        (show (t, y) ∈ Icc a b ×ˢ K from ⟨ht, hy⟩))).trans (le_max_right _ _)
    · simp only [hzero t y hy, norm_zero]
      exact le_max_left _ _
  obtain ⟨B, hB, hbound⟩ := hDb
  refine ⟨⟨B, hB⟩, ?_⟩
  intro t ht
  have hXt : ContDiff ℝ ∞ (X t) :=
    hX.comp (contDiff_const.prodMk contDiff_id)
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (hXt.differentiable (by simp))
  intro y
  exact_mod_cast hbound t ht y
