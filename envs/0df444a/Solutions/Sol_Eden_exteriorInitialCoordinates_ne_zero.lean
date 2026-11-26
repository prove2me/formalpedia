-- Prove2me | solution 1 for Eden.exteriorInitialCoordinates_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:50.010025+00:00
-- url     : https://prove2.me/submissions/9f198d7e-e042-4055-b5ba-633b0833b0b8

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry
import Theorems.Thm_Eden_norm_exterior_map_isometry

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) : exteriorInitialCoordinates k p v ≠ 0 := by
  intro h
  have hz : exteriorPower.map k (radialFrame p).symm.toLinearMap v = 0 :=
    (exteriorBasis k).repr.injective (h.trans (map_zero _).symm)
  have hn := norm_exterior_map_isometry k (radialFrame p).symm v
  rw [hz, norm_zero] at hn
  exact hv (norm_eq_zero.mp hn.symm)
end Eden
