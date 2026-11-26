-- Prove2me | solution 1 for EdenVerified.p01_exists_planar_angular_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:03.868124+00:00
-- url     : https://prove2.me/submissions/aab98d98-5df4-490e-8f91-86850505f7e3

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_exists_planar_angular_lift


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (Ω x y : ℝ) (hxy : x ^ 2 + y ^ 2 ≠ 0),
    ∃ θ : ℝ,
      (∀ t : ℝ, HasDerivAt (fun τ => θ + Ω * τ) Ω t) ∧
      ∀ t : ℝ, 0 ≤ t →
        0 < radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) ∧
        planarX Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.cos (θ + Ω * t) ∧
        planarY Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.sin (θ + Ω * t) :=
  @Eden.exists_planar_angular_lift
end EdenVerified
