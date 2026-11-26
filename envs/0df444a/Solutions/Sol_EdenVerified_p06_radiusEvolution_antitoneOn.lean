-- Prove2me | solution 1 for EdenVerified.p06_radiusEvolution_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:03.151389+00:00
-- url     : https://prove2.me/submissions/8f184b04-f7e9-4193-831a-6b2d12a6f4a5

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_antitoneOn


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {R : ℝ} (hR : Real.sqrt 2 ≤ R),
    AntitoneOn (fun t => radiusEvolution t R) (Ici 0) :=
  @Eden.radiusEvolution_antitoneOn
end EdenVerified
