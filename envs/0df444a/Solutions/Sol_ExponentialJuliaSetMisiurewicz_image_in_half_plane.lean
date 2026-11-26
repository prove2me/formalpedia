-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.image_in_half_plane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:30.155292+00:00
-- url     : https://prove2.me/submissions/4a34a726-623c-4bf5-a2d4-e9420dce0a63

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_continuous_expIterate


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {V : Set ℂ} (hVconn : IsConnected V)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0) (n : ℕ) :
    (∀ z ∈ V, 0 < (expIterate n z).im) ∨ (∀ z ∈ V, (expIterate n z).im < 0) := by
  have hcont : ContinuousOn (fun y => (expIterate n y).im) V :=
    (Complex.continuous_im.comp (continuous_expIterate n)).continuousOn
  by_cases hpos : ∀ z ∈ V, 0 < (expIterate n z).im
  · exact Or.inl hpos
  refine Or.inr ?_
  push Not at hpos
  obtain ⟨b, hb, hble⟩ := hpos
  have hbneg : (expIterate n b).im < 0 := lt_of_le_of_ne hble (hnoreal n b hb)
  intro z hz
  by_contra hzge
  push Not at hzge
  have hzpos : 0 < (expIterate n z).im :=
    lt_of_le_of_ne hzge (Ne.symm (hnoreal n z hz))
  obtain ⟨y, hy, hyval⟩ :=
    hVconn.isPreconnected.intermediate_value hb hz hcont
      ⟨le_of_lt hbneg, le_of_lt hzpos⟩
  exact hnoreal n y hy hyval
end ExponentialJuliaSetMisiurewicz
