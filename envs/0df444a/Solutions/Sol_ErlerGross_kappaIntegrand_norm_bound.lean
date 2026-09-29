-- Prove2me | solution 1 for ErlerGross.kappaIntegrand_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:41:44.353443+00:00
-- url     : https://prove2.me/submissions/06b76d1f-128f-4a02-b439-a6d4a2b7e7cc

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
