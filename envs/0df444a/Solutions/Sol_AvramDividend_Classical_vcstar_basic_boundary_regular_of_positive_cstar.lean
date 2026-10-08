-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_basic_boundary_regular_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:56:44.370314+00:00
-- url     : https://prove2.me/submissions/7b1c7b0e-9e2e-4dba-a387-9f0e41c10365
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      ∀ y < 0, vcstar W y = 0 := by
  let c : ℝ := (cstar W).toReal
  have hctop : cstar W ≠ ⊤ := ne_of_lt hc
  have hcne : cstar W ≠ 0 := ne_of_gt hcpos
  have hcR : 0 < c := by
    exact ENNReal.toReal_pos hcne hctop
  have hdc : 0 < deriv W c :=
    scaleDeriv_pos X hX q hq W hW c hcR
  have hscale : scaleDeriv W c = ((deriv W c : ℝ) : EReal) := by
    simp [scaleDeriv, c, hcR.ne']
  have hdiv (y : ℝ) : divE (W y) (scaleDeriv W c) = W y / deriv W c := by
    simp [hscale, divE]

  have hcont0base :
      ContinuousWithinAt (fun y : ℝ => W y / deriv W c) (Ici 0) 0 := by
    exact (hW.2.2.1 0 (by simp)).div_const (deriv W c)
  have hlocal0 :
      vcstar W =ᶠ[𝓝[Ici 0] 0] (fun y : ℝ => W y / deriv W c) := by
    filter_upwards
      [self_mem_nhdsWithin,
       mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hcR)] with y hy0 hyc
    change 0 ≤ y at hy0
    change y ≤ c at hyc
    simp [vcstar, barrierValue, c, not_lt.mpr hy0, hyc, hdiv]
  have hcont0 : ContinuousWithinAt (vcstar W) (Ici 0) 0 := by
    exact hcont0base.congr_of_eventuallyEq_of_mem hlocal0 (by simp)

  have hcont : ContinuousOn (vcstar W) (Ici 0) := by
    intro x hx
    change 0 ≤ x at hx
    rcases eq_or_lt_of_le hx with rfl | hxpos
    · exact hcont0
    · exact
        (vcstar_deriv_ge_one X hX q hq W hW x hxpos).1.continuousAt.continuousWithinAt

  have hzero : 0 ≤ vcstar W 0 := by
    have hW0 : 0 ≤ W 0 := hW.2.1 0 (le_refl 0)
    have hv0 : vcstar W 0 = W 0 / deriv W c := by
      simp [vcstar, barrierValue, c, hcR.le, hdiv]
    rw [hv0]
    exact div_nonneg hW0 hdc.le

  have hneg : ∀ y < 0, vcstar W y = 0 := by
    intro y hy
    simp [vcstar, barrierValue, hy]

  exact ⟨hcont, hzero, hneg⟩
