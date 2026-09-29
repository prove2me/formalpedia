-- Prove2me | solution 2 for ErlerGross.kappaIntegrand_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:42:54.002986+00:00
-- url     : https://prove2.me/submissions/1494a594-b3b1-4d90-8a85-f5fa3bac903f

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_kappaIntegrand_hyperbolic_majorant
import Theorems.Thm_ErlerGross_kappaIntegrand_majorant_decay

open Real

theorem solution :
    forall kappa : Real, abs (ErlerGross.kappaIntegrand kappa) <=
      (1 + abs kappa) ^ (-2 : Real) := by
  intro kappa
  exact le_trans (ErlerGross.kappaIntegrand_hyperbolic_majorant kappa)
    (ErlerGross.kappaIntegrand_majorant_decay kappa)
