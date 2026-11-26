-- Prove2me | solution 1 for EdenVerified.p25_fifth_eq_zero_of_evolution_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:17:11.023332+00:00
-- url     : https://prove2.me/submissions/4d0c9b19-1b86-4102-aa0e-cd72a7de5450

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_fifth_eq_zero_of_evolution_return


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    p 4 = 0 :=
  @Eden.fifth_eq_zero_of_evolution_return
end EdenVerified
