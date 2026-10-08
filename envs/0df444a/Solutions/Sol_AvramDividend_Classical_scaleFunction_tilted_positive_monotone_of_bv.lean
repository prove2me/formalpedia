-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:36:26.607979+00:00
-- url     : https://prove2.me/submissions/049c1655-fd61-4be3-827b-65d31a7d37fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_tilted_cumulative_laplace_representation
import Theorems.Thm_AvramDividend_Classical_positive_tilted_of_laplace_cumulative_identification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  obtain ⟨β, φ, b, hφ, hfin, hatom, hlap⟩ :=
    bv_tilted_cumulative_laplace_representation X hX q hq W hW hbv
  have hcontW : ContinuousOn W (Ioi (0 : ℝ)) := by
    apply (hW.2.2.1).mono
    intro x hx
    exact Set.mem_Ici.mpr (le_of_lt hx)
  have hcontExp : Continuous (fun x : ℝ => Real.exp (-φ * x)) := by
    fun_prop
  have htiltcont :
      ContinuousOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) :=
    hcontExp.continuousOn.mul hcontW
  have htiltnonneg : ∀ x : ℝ, 0 < x →
      0 ≤ Real.exp (-φ * x) * W x := by
    intro x hx
    have hexp : 0 ≤ Real.exp (-φ * x) := by positivity
    exact mul_nonneg hexp (hW.2.1 x hx.le)
  obtain ⟨hpos, hmono⟩ :=
    positive_tilted_of_laplace_cumulative_identification
      β φ b hφ hfin hatom W htiltcont htiltnonneg hlap
  exact ⟨hpos, φ, hφ, hmono⟩
