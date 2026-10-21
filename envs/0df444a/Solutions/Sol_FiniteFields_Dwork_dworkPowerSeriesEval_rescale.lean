-- Prove2me | solution 1 for FiniteFields.Dwork.dworkPowerSeriesEval_rescale
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:40:37.887485+00:00
-- url     : https://prove2.me/submissions/2049c818-ba7c-47fc-9e91-52c6c2dd8a6c

import Mathlib
import Definitions.Def_FiniteFields_Dwork_ArtinHasse
open Filter PowerSeries
open scoped NNReal Topology
open FiniteFields.Dwork
variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k]
theorem solution
    (f : (DworkCyclotomicField k p)⟦X⟧)
    (r x : DworkCyclotomicField k p) :
    dworkPowerSeriesEval k p (PowerSeries.rescale r f) x =
      dworkPowerSeriesEval k p f (r * x) := by
  unfold dworkPowerSeriesEval
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_rescale, mul_pow]
  ring
