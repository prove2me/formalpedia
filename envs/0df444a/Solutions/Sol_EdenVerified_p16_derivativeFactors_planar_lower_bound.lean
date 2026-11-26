-- Prove2me | solution 1 for EdenVerified.p16_derivativeFactors_planar_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:26:22.079899+00:00
-- url     : https://prove2.me/submissions/903a266d-6d6e-4798-9388-3c4c66bfb9ee

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_derivativeFactors_planar_lower_bound


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4),
    Real.exp (-4 * t) ≤ derivativeFactors c t p i.castSucc :=
  @Eden.derivativeFactors_planar_lower_bound
end EdenVerified
