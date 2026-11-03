-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:40:26.647142+00:00
-- url     : https://prove2.me/submissions/6c0d481d-166a-471c-89d7-8f65b47353b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_deriv_bounded_on_compact_of_contDiff_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (cap l r : ℝ)
    (hlr : l < r) (hsub : Icc l r ⊆ Ioo 0 cap)
    (hwC1 : X.BoundedVariation → ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
        |w s - w t| ≤ L * |s - t| := by
  obtain ⟨M, hM, hMderiv⟩ :=
    deriv_bounded_on_compact_of_contDiff_one w cap l r hlr hsub (hwC1 hBV)
  let K : ℝ≥0 := ⟨M, hM⟩
  have hcoeff : (K : ℝ) = M := rfl
  have hK : ∀ y ∈ Icc l r, ‖deriv w y‖₊ ≤ K := by
    intro y hy
    apply NNReal.coe_le_coe.mp
    simpa [hcoeff, Real.norm_eq_abs] using hMderiv y hy
  have hDiff : ∀ y ∈ Icc l r, DifferentiableAt ℝ w y := by
    intro y hy
    have hd : DifferentiableWithinAt ℝ w (Ioo 0 cap) y :=
      (hwC1 hBV).differentiableOn_one y (hsub hy)
    exact hd.differentiableAt (isOpen_Ioo.mem_nhds (hsub hy))
  have hLip : LipschitzOnWith K w (Icc l r) :=
    (convex_Icc l r).lipschitzOnWith_of_nnnorm_deriv_le hDiff hK
  refine ⟨M, hM, ?_⟩
  intro s hs t ht
  simpa only [Real.dist_eq, hcoeff] using hLip.dist_le_mul s hs t ht
