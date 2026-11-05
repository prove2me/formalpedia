-- Prove2me | solution 1 for BHTOpinion.Continuum.prop3c_fixed_point_in_Fbar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:43:01.648077+00:00
-- url     : https://prove2.me/submissions/63d70f54-db94-47e7-b6ea-f8a7f03d50d6

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model
import Theorems.Thm_BHTOpinion_Continuum_prop3a_limit_in_Fbar

open MeasureTheory Filter Topology

open BHTOpinion.Continuum in
theorem solution (s : ℝ → ℝ) (hs : InX s) (hfix : IsFixedPoint s) :
    InFbar s := by
  obtain ⟨y', hy'F, hy'eq⟩ := prop3a_limit_in_Fbar s (fun _ => s) hfix.2.1
    (fun _ _ => hs) s (Filter.Eventually.of_forall (fun _ => tendsto_const_nhds))
  refine ⟨hs, ?_⟩
  have h1 : ∀ᵐ p ∂((volume.restrict I).prod (volume.restrict I)), y' p.1 = s p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hy'eq
  have h2 : ∀ᵐ p ∂((volume.restrict I).prod (volume.restrict I)), y' p.2 = s p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hy'eq
  filter_upwards [hy'F.2, h1, h2] with p hp e1 e2
  rw [← e1, ← e2]; exact hp
