-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:35:46.978639+00:00
-- url     : https://prove2.me/submissions/7f18e772-e59d-477a-bfa9-eed11fea5a69

import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- A genuine original C1 candidate on an ambient domain is Lipschitz
on every compact reserve interval contained in that domain. -/
theorem solution
    (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (lo hi : ℝ)
    (hsub : Set.Icc lo hi ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
        |w x - w y| ≤ L * |x - y| := by
  have hC1 : ContDiffOn ℝ 1 w (Set.Icc lo hi) :=
    hw.mono hsub
  have hLocal : LocallyLipschitzOn (Set.Icc lo hi) w :=
    ContDiffOn.locallyLipschitzOn (convex_Icc lo hi) hC1
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      isCompact_Icc hLocal
  refine ⟨(K : ℝ), NNReal.coe_nonneg K, ?_⟩
  intro x hx y hy
  have h := hK.dist_le_mul x hx y hy
  simpa only [Real.dist_eq] using h
