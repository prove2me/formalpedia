-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T14:44:37.832991+00:00
-- url     : https://prove2.me/submissions/6262ff90-0e8c-4517-aaf7-2eaf78be2292

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → 0 ≤ deriv W x := by
  intro x hx
  unfold IsScaleFunction at hW
  have hmono : MonotoneOn W (Ici (0 : ℝ)) := hW.2.2.2.1
  have hnonneg : 0 ≤ derivWithin W (Ici (0 : ℝ)) x :=
    hmono.derivWithin_nonneg
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hx)] at hnonneg
  exact hnonneg
