-- Prove2me | solution 1 for EdenVerified.p07_attractor_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:17.018415+00:00
-- url     : https://prove2.me/submissions/4076b86d-10a9-483a-8a4d-30d98d0a5b68

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_attractor_minimal


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} {C : Set PhaseSpace} (hcompact : IsCompact C)
    (hC : UniformlyAttractsBounded c C),
    attractor ⊆ C :=
  @Eden.attractor_minimal
end EdenVerified
