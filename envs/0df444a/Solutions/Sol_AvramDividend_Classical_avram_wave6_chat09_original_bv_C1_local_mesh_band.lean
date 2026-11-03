-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_bv_C1_local_mesh_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:33:28.817742+00:00
-- url     : https://prove2.me/submissions/36f826bd-6bb8-4e8c-9ada-393dc538d49d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A strict original-source BV reserve point has a compact C1 mesh
neighbourhood with one derivative bound usable for the stochastic grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (y : ℝ)
    (hy : 0 < y ∧ ENNReal.ofReal y < C)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C}) :
    ∃ δ : ℝ, 0 < δ ∧
      Icc (y - δ) (y + δ) ⊆
        {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} ∧
      ∃ K : ℝ≥0,
        (∀ z ∈ Icc (y - δ) (y + δ), ‖deriv w z‖₊ ≤ K) ∧
        LipschitzOnWith K w (Icc (y - δ) (y + δ)) := by
  let U : Set ℝ := {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C}
  have hOpen : IsOpen U :=
    avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hOpen) y hy
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ_lt : δ < ε := by dsimp [δ]; linarith
  have hlr : y - δ < y + δ := by linarith
  have hBand : Icc (y - δ) (y + δ) ⊆ U := by
    intro z hz
    apply hball
    change dist z y < ε
    rw [Real.dist_eq]
    have hzabs : |z - y| ≤ δ := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    exact lt_of_le_of_lt hzabs hδ_lt
  have hC1K : ContDiffOn ℝ 1 w (Icc (y - δ) (y + δ)) :=
    (hwC1 hBV).mono hBand
  have huniq : UniqueDiffOn ℝ (Icc (y - δ) (y + δ)) :=
    uniqueDiffOn_Icc hlr
  have hcont :
      ContinuousOn
        (fun z => ‖iteratedDerivWithin 1 w (Icc (y - δ) (y + δ)) z‖₊)
        (Icc (y - δ) (y + δ)) := by
    exact (ContDiffOn.continuousOn_iteratedDerivWithin
      hC1K (by norm_num) huniq).nnnorm
  have hcontReal :
      ContinuousOn
        (fun z => (‖iteratedDerivWithin 1 w (Icc (y - δ) (y + δ)) z‖₊ : ℝ))
        (Icc (y - δ) (y + δ)) :=
    NNReal.continuous_coe.comp_continuousOn hcont
  have hKne : (Icc (y - δ) (y + δ)).Nonempty :=
    ⟨y, ⟨by linarith [hδ], by linarith [hδ]⟩⟩
  obtain ⟨zM, hzM, hmax⟩ :
      ∃ zM ∈ Icc (y - δ) (y + δ),
        ∀ z ∈ Icc (y - δ) (y + δ),
          (‖iteratedDerivWithin 1 w (Icc (y - δ) (y + δ)) z‖₊ : ℝ) ≤
            (‖iteratedDerivWithin 1 w (Icc (y - δ) (y + δ)) zM‖₊ : ℝ) :=
    isCompact_Icc.exists_isMaxOn hKne hcontReal
  let K : ℝ≥0 := ‖iteratedDerivWithin 1 w (Icc (y - δ) (y + δ)) zM‖₊
  have hK : ∀ z ∈ Icc (y - δ) (y + δ), ‖deriv w z‖₊ ≤ K := by
    intro z hz
    have hzC1 : ContDiffAt ℝ 1 w z :=
      (hwC1 hBV).contDiffAt (hOpen.mem_nhds (hBand hz))
    have hzEq :
        iteratedDerivWithin 1 w (Icc (y - δ) (y + δ)) z = deriv w z := by
      rw [iteratedDerivWithin_eq_iteratedDeriv huniq hzC1 hz]
      simp
    apply NNReal.coe_le_coe.mp
    rw [← hzEq]
    exact hmax z hz
  have hDiff : ∀ z ∈ Icc (y - δ) (y + δ), DifferentiableAt ℝ w z := by
    intro z hz
    have hd : DifferentiableWithinAt ℝ w U z :=
      (hwC1 hBV).differentiableOn_one z (hBand hz)
    exact hd.differentiableAt (hOpen.mem_nhds (hBand hz))
  have hLip : LipschitzOnWith K w (Icc (y - δ) (y + δ)) :=
    (convex_Icc (y - δ) (y + δ)).lipschitzOnWith_of_nnnorm_deriv_le hDiff hK
  exact ⟨δ, hδ, hBand, K, hK, hLip⟩
