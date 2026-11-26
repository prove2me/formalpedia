-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegral_cons_nil_eq_integral_partialDeriv_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:57.111369+00:00
-- url     : https://prove2.me/submissions/113e1a83-6d06-4d9e-aef7-6ad47a0bfd0e

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_cons_nil_eq_integral_partialDeriv_standardInterp

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    {F F' : Forest V} {e : Edge V} (step : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step (OrderedGrowth.nil F')).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ), partialDeriv e ρ
        (F'.standardInterp (step.extendParam u t)) :=
  branchIntegralAux_cons_nil_eq_integral_partialDeriv_standardInterp
    step 1 u ρ
end BKAR.Forest.OrderedGrowth
