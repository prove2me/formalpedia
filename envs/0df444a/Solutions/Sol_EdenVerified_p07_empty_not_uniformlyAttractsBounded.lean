-- Prove2me | solution 1 for EdenVerified.p07_empty_not_uniformlyAttractsBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:22.81743+00:00
-- url     : https://prove2.me/submissions/02ce50f3-871d-4834-a7bf-2e8026e121c8

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_empty_not_uniformlyAttractsBounded


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ),
    ¬UniformlyAttractsBounded c (∅ : Set PhaseSpace) :=
  @Eden.empty_not_uniformlyAttractsBounded
end EdenVerified
