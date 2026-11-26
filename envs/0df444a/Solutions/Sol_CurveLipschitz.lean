-- Prove2me | solution 1 for CurveLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:48:20.170732+00:00
-- url     : https://prove2.me/submissions/7646e365-3415-4f41-9563-50890feaaf01

import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_CurveLipschitz

set_option autoImplicit false
open MeasureTheory Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) :
    LipschitzWith 1 γ.toFun := by
-- BODY
  have step1 : ∀ {s t : ℝ}, s ∈ Set.Icc (0:ℝ) γ.len → t ∈ Set.Icc (0:ℝ) γ.len →
      edist (γ.toFun s) (γ.toFun t) ≤ ENNReal.ofReal |s - t| := by
    intro s t hs ht
    rcases le_total s t with h | h
    · have hv := γ.unitSpeed hs ht
      have hle : edist (γ.toFun s) (γ.toFun t) ≤
          eVariationOn γ.toFun (Set.Icc 0 γ.len ∩ Icc s t) :=
        eVariationOn.edist_le _ ⟨hs, le_refl s, h⟩ ⟨ht, h, le_refl t⟩
      rw [hv] at hle
      simpa [abs_of_nonpos (sub_nonpos.mpr h), one_mul] using hle
    · have hv := γ.unitSpeed ht hs
      have hle : edist (γ.toFun t) (γ.toFun s) ≤
          eVariationOn γ.toFun (Set.Icc 0 γ.len ∩ Icc t s) :=
        eVariationOn.edist_le _ ⟨ht, le_refl t, h⟩ ⟨hs, h, le_refl s⟩
      rw [hv] at hle
      rw [edist_comm]
      simpa [abs_of_nonneg (sub_nonneg.mpr h), one_mul] using hle
  have hclamp : LipschitzWith 1 (fun t : ℝ => min γ.len (max 0 t)) :=
    (LipschitzWith.id.const_max (0:ℝ)).const_min γ.len
  intro s t
  rw [γ.clamped s, γ.clamped t]
  have hs : min γ.len (max 0 s) ∈ Set.Icc (0:ℝ) γ.len :=
    ⟨le_min γ.len_nonneg (le_max_left _ _), min_le_left _ _⟩
  have ht : min γ.len (max 0 t) ∈ Set.Icc (0:ℝ) γ.len :=
    ⟨le_min γ.len_nonneg (le_max_left _ _), min_le_left _ _⟩
  refine (step1 hs ht).trans ?_
  have := hclamp s t
  simpa [edist_dist, Real.dist_eq, ENNReal.ofReal] using this
