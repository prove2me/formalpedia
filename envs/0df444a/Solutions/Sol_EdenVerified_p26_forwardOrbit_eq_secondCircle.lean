-- Prove2me | solution 1 for EdenVerified.p26_forwardOrbit_eq_secondCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:18:44.113703+00:00
-- url     : https://prove2.me/submissions/19e896ed-627c-4b66-8c0a-da1f264dc2af

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_forwardOrbit_eq_secondCircle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ secondCircle s),
    forwardOrbit c p = secondCircle s :=
  @Eden.forwardOrbit_eq_secondCircle
end EdenVerified
