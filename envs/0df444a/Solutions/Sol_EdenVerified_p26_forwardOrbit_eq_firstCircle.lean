-- Prove2me | solution 1 for EdenVerified.p26_forwardOrbit_eq_firstCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:18:23.943624+00:00
-- url     : https://prove2.me/submissions/b1064795-7bd1-4f37-8df5-c6d72d700846

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_forwardOrbit_eq_firstCircle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ firstCircle s),
    forwardOrbit c p = firstCircle s :=
  @Eden.forwardOrbit_eq_firstCircle
end EdenVerified
