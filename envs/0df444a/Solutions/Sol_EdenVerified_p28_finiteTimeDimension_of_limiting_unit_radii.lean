-- Prove2me | solution 1 for EdenVerified.p28_finiteTimeDimension_of_limiting_unit_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:55.493547+00:00
-- url     : https://prove2.me/submissions/61990107-3950-4348-8d00-b1f9789d7f4b

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_finiteTimeDimension_of_limiting_unit_radii


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1),
    finiteTimeDimension c t p = targetDimension c :=
  @Eden.finiteTimeDimension_of_limiting_unit_radii
end EdenVerified
