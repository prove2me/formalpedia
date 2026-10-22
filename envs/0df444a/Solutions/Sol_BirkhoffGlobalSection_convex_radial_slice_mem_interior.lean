-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_radial_slice_mem_interior
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:13:19.330974+00:00
-- url     : https://prove2.me/submissions/e59872f1-6028-4386-b1d9-8b51403b1184

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_convex_radial_slice_mem_interior

theorem solution :
∀ {E : Type u_convex_radial_slice_mem_interior}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (hK : Convex ℝ K)
    (h0 : (0 : E) ∈ interior K) (y : E) (hy : y ∈ closure K)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1),
    t • y ∈ interior K := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0, 0, u_convex_radial_slice_mem_interior}.2.2.2.2.2.2.2.2.2.2.2.1
