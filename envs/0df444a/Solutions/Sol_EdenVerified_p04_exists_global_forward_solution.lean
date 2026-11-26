-- Prove2me | solution 1 for EdenVerified.p04_exists_global_forward_solution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:10:00.802065+00:00
-- url     : https://prove2.me/submissions/7d5dde74-cb92-4d25-9600-b3e7d84ed5ee

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_exists_global_forward_solution


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) (p : PhaseSpace),
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t :=
  @Eden.exists_global_forward_solution
end EdenVerified
