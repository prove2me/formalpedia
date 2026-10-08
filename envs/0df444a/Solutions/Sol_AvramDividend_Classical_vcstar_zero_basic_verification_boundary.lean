-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_zero_basic_verification_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:23:55.78198+00:00
-- url     : https://prove2.me/submissions/31c8cea0-f236-4739-87d2-65469a4b48ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc0 : cstar W = 0) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      ∀ y < 0, vcstar W y = 0 := by
  have hlin :
      ContinuousOn (fun z : ℝ => z + barrierValue W 0 0) (Ici 0) := by
    fun_prop
  have hcontinuous : ContinuousOn (vcstar W) (Ici 0) := by
    apply hlin.congr
    intro z hz
    have hz0 : 0 ≤ z := hz
    simpa [vcstar, hc0] using
      (barrierValue_zero_affine_nonnegative W z hz0)
  have hnonneg : 0 ≤ vcstar W 0 := by
    have hbound := barrierValue_zero_boundary_nonneg X hX q hq W hW
    simpa [vcstar, hc0] using hbound
  refine ⟨hcontinuous, hnonneg, ?_⟩
  intro y hy
  exact vcstar_eq_zero_of_neg W y hy
