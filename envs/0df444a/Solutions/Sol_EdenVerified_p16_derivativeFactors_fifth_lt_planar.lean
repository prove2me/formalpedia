-- Prove2me | solution 1 for EdenVerified.p16_derivativeFactors_fifth_lt_planar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:26:47.179847+00:00
-- url     : https://prove2.me/submissions/88e1aed1-15db-4f2d-94e5-470aa537cad3

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_derivativeFactors_fifth_lt_planar


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4),
    derivativeFactors c t p 4 < derivativeFactors c t p i.castSucc :=
  @Eden.derivativeFactors_fifth_lt_planar
end EdenVerified
