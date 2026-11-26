-- Prove2me | solution 1 for EdenVerified.p06_bounded_set_radius_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:27.760408+00:00
-- url     : https://prove2.me/submissions/3e0c3efe-afab-49ed-9987-100169796b46

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_bounded_set_radius_bounds


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {B : Set PhaseSpace} (hB : Bornology.IsBounded B),
    ∃ M W : ℝ, Real.sqrt 2 < M ∧ 0 ≤ W ∧ ∀ p ∈ B,
      Real.sqrt (radiusSq₁ p) ≤ M ∧ Real.sqrt (radiusSq₂ p) ≤ M ∧ |p 4| ≤ W :=
  @Eden.bounded_set_radius_bounds
end EdenVerified
