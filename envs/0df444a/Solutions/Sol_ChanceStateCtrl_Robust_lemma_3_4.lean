-- Prove2me | solution 1 for ChanceStateCtrl.Robust.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:43:05.307385+00:00
-- url     : https://prove2.me/submissions/0085d7ce-3159-4112-9aa1-bd389a31c9bf

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory

theorem solution {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : P.map ξ ≪ volume) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : LowerSemicontinuous h) :
    (∀ᵐ w ∂P, h (ξ w) ≤ 0) ↔ ∀ z ∈ (P.map ξ).support, h z ≤ 0 := by
  constructor
  · intro hae z hz
    by_contra hpos
    push Not at hpos
    have hUo : IsOpen (h ⁻¹' Set.Ioi 0) := hh.isOpen_preimage 0
    have hU : h ⁻¹' Set.Ioi 0 ∈ nhds z := hUo.mem_nhds hpos
    have h1 := (Measure.mem_support_iff_forall z).1 hz _ hU
    rw [Measure.map_apply hξ hUo.measurableSet] at h1
    rw [ae_iff] at hae
    have : ξ ⁻¹' (h ⁻¹' Set.Ioi 0) = {w | ¬ h (ξ w) ≤ 0} := by
      ext w; simp
    rw [this, hae] at h1
    exact lt_irrefl _ h1
  · intro hsupp
    have hs : ∀ᵐ z ∂(P.map ξ), z ∈ (P.map ξ).support := Measure.support_mem_ae
    filter_upwards [ae_of_ae_map hξ.aemeasurable hs] with w hw
    exact hsupp _ hw
