-- Prove2me | solution 1 for FiniteEnergyPlane.dlambdaEnergy_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-22T19:09:13.846071+00:00
-- url     : https://prove2.me/submissions/9af8a685-c8dd-45af-9ea2-9afcd899ea0a

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib



/-! The `dλ`-energy under a translation `z ↦ z + B` of the domain. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem dlambdaEnergy_comp_add_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (B : ℂ) (s : Set ℂ) :
    dlambdaEnergy H s (fun z => u (z + B)) = dlambdaEnergy H ((fun y => y + B) '' s) u := by
  have hd : ∀ z, dlambdaDensity H (fun z => u (z + B)) z = dlambdaDensity H u (z + B) := by
    intro z
    unfold dlambdaDensity ds dt
    rw [fderiv_comp_add_right (f := fun y => proj H (u y)) B]
  unfold dlambdaEnergy
  simp_rw [hd]
  exact (measurePreserving_add_right volume B).setLIntegral_comp_emb
    (MeasurableEquiv.addRight B).measurableEmbedding
    (fun z => ENNReal.ofReal (dlambdaDensity H u z)) s

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (B : ℂ) (s : Set ℂ) :
    dlambdaEnergy H s (fun z => u (z + B)) = dlambdaEnergy H ((fun y => y + B) '' s) u :=
  dlambdaEnergy_comp_add_aux H u B s
