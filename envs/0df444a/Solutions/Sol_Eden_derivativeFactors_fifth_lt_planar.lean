-- Prove2me | solution 1 for Eden.derivativeFactors_fifth_lt_planar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:13:32.807854+00:00
-- url     : https://prove2.me/submissions/64f65d9f-f0ab-450a-aff4-01c06836f963

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
import Theorems.Thm_Eden_exp_fifth_lt_planar_bound
import Theorems.Thm_Eden_derivativeFactors_planar_lower_bound

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 4) :
    derivativeFactors c t p 4 < derivativeFactors c t p i.castSucc :=
  (exp_fifth_lt_planar_bound hc ht).trans_le (derivativeFactors_planar_lower_bound c ht.le hp i)
end Eden
