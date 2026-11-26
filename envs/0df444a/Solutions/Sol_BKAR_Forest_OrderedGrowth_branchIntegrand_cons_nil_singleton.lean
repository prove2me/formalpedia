-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegrand_cons_nil_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:54.022673+00:00
-- url     : https://prove2.me/submissions/418ad6df-f398-42d1-a6ff-9756ef309b79

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_cons_cons_eq_tail_partialDeriv

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution {F F' : Forest V} {e : Edge V}
    (step : EdgeExtension F F' e) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    (OrderedGrowth.cons step (OrderedGrowth.nil F')).branchIntegrand u ρ [t] =
      partialDeriv e ρ (F'.standardInterp (step.extendParam u t)) := by
  rw [branchIntegrand_cons_cons_eq_tail_partialDeriv]
  rfl
end BKAR.Forest.OrderedGrowth
