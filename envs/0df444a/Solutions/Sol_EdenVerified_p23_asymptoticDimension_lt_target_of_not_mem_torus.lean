-- Prove2me | solution 1 for EdenVerified.p23_asymptoticDimension_lt_target_of_not_mem_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:37:47.792368+00:00
-- url     : https://prove2.me/submissions/e1604591-2f0f-4313-abba-74b2678f8032

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_lt_target_of_not_mem_torus


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus),
    asymptoticDimension c p < targetDimension c :=
  @Eden.asymptoticDimension_lt_target_of_not_mem_torus
end EdenVerified
