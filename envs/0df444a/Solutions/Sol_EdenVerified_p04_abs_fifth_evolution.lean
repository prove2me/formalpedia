-- Prove2me | solution 1 for EdenVerified.p04_abs_fifth_evolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:47.994032+00:00
-- url     : https://prove2.me/submissions/2feb81d7-6283-4a6e-9dfd-ea33b2bd4935

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_abs_fifth_evolution


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c t : ℝ) (p : PhaseSpace),
    |evolution c t p 4| = Real.exp (-c * t) * |p 4| :=
  @Eden.abs_fifth_evolution
end EdenVerified
