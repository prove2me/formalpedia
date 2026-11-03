-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:46:36.489959+00:00
-- url     : https://prove2.me/submissions/b1d37237-5ae4-46ec-be68-fd79da403c7e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

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
    (w : ℝ → ℝ) (C : ℝ≥0∞) (l r : ℝ) (hlr : l < r)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc l r ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
        |w s - w t| ≤ L * |s - t| := by
  have hC1K : ContDiffOn ℝ 1 w (Icc l r) :=
    (hwC1 hBV).mono hBand
  have huniq : UniqueDiffOn ℝ (Icc l r) :=
    uniqueDiffOn_Icc hlr
  have hcont :
      ContinuousOn
        (fun z => ‖iteratedDerivWithin 1 w (Icc l r) z‖₊)
        (Icc l r) := by
    exact (ContDiffOn.continuousOn_iteratedDerivWithin
      hC1K (by norm_num) huniq).nnnorm
  have hcontReal :
      ContinuousOn
        (fun z => (‖iteratedDerivWithin 1 w (Icc l r) z‖₊ : ℝ))
        (Icc l r) :=
    NNReal.continuous_coe.comp_continuousOn hcont
  have hKne : (Icc l r).Nonempty :=
    ⟨l, ⟨le_rfl, hlr.le⟩⟩
  obtain ⟨zM, hzM, hmax⟩ :
      ∃ zM ∈ Icc l r, ∀ z ∈ Icc l r,
        (‖iteratedDerivWithin 1 w (Icc l r) z‖₊ : ℝ) ≤
          (‖iteratedDerivWithin 1 w (Icc l r) zM‖₊ : ℝ) :=
    isCompact_Icc.exists_isMaxOn hKne hcontReal
  let K : ℝ≥0 := ‖iteratedDerivWithin 1 w (Icc l r) zM‖₊
  have hK : ∀ y ∈ Icc l r, ‖deriv w y‖₊ ≤ K := by
    intro y hy
    have hyC1 : ContDiffAt ℝ 1 w y :=
      (hwC1 hBV).contDiffAt (hOpen.mem_nhds (hBand hy))
    have hyEq :
        iteratedDerivWithin 1 w (Icc l r) y = deriv w y := by
      rw [iteratedDerivWithin_eq_iteratedDeriv huniq hyC1 hy]
      simp
    apply NNReal.coe_le_coe.mp
    rw [← hyEq]
    exact hmax y hy
  have hDiff : ∀ y ∈ Icc l r, DifferentiableAt ℝ w y := by
    intro y hy
    have hd : DifferentiableWithinAt ℝ w
        {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} y :=
      (hwC1 hBV).differentiableOn_one y (hBand hy)
    exact hd.differentiableAt (hOpen.mem_nhds (hBand hy))
  have hLip : LipschitzOnWith K w (Icc l r) :=
    (convex_Icc l r).lipschitzOnWith_of_nnnorm_deriv_le hDiff hK
  refine ⟨(K : ℝ), NNReal.coe_nonneg K, ?_⟩
  intro s hs t ht
  simpa only [Real.dist_eq] using hLip.dist_le_mul s hs t ht
