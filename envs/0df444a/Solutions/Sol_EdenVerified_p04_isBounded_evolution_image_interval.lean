-- Prove2me | solution 1 for EdenVerified.p04_isBounded_evolution_image_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:54.956094+00:00
-- url     : https://prove2.me/submissions/eaf878fc-b13f-481f-a897-3fe6761fc187

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_isBounded_evolution_image_interval


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c T : ℝ) (p : PhaseSpace),
    Bornology.IsBounded ((fun t => evolution c t p) '' Icc 0 T) :=
  @Eden.isBounded_evolution_image_interval
end EdenVerified
