-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.integral_partialDeriv_interpWithFill_eq_singletonGrowth_branchIntegral_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:13.476215+00:00
-- url     : https://prove2.me/submissions/3ce1ff33-f0e6-47c4-bd6e-d8c44857879a

import Definitions.Def_BKAR_OrderedBranch
import Definitions.Def_BKAR_OrderedTerminal
import Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_branchIntegral_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution
    (h : ActiveExtension F e) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (hterm : h.forest.activeEdges = ∅) :
    (∫ t in 0..(1 : ℝ), partialDeriv e ρ
        (h.forest.interpWithFill (h.extension.extendParam u t) t)) =
      h.singletonGrowth.branchIntegral u ρ :=
  (h.singletonGrowth_branchIntegral_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty
    u ρ hterm).symm
end BKAR.Forest.ActiveExtension
