-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.integral_partialDeriv_interpWithFill_eq_singletonGrowth_branchIntegralAux_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:50.365402+00:00
-- url     : https://prove2.me/submissions/4c48f7a4-aa7d-45b7-a2fc-7a0eba3de128

import Definitions.Def_BKAR_OrderedBranch
import Definitions.Def_BKAR_OrderedTerminal
import Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_branchIntegralAux_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution
    (h : ActiveExtension F e) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (hterm : h.forest.activeEdges = ∅) :
    (∫ t in 0..top, partialDeriv e ρ
        (h.forest.interpWithFill (h.extension.extendParam u t) t)) =
      h.singletonGrowth.branchIntegralAux top u ρ :=
  (h.singletonGrowth_branchIntegralAux_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty
    top u ρ hterm).symm
end BKAR.Forest.ActiveExtension
