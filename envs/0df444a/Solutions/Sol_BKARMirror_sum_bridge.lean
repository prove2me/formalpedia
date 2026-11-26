-- Prove2me | solution 1 for BKARMirror.sum_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:07.345057+00:00
-- url     : https://prove2.me/submissions/8d7bf54f-7794-430a-9162-06db415b0fe1

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
import Theorems.Thm_BKARMirror_cubeContribution_bridge

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKARMirror
theorem _root_.solution (ρ : (Edge V → ℝ) → ℝ) (hρ : ContDiffHyp ρ) :
    (∑ J : ForestIndex V, cubeContribution J ρ) =
      ∑ I : BKAR.ForestIndex V, I.cubeContribution ρ :=
  calc (∑ J : ForestIndex V, cubeContribution J ρ)
      = ∑ J : ForestIndex V, (indexEquiv J).cubeContribution ρ :=
        Finset.sum_congr rfl (fun J _ => cubeContribution_bridge J ρ hρ)
    _ = ∑ I : BKAR.ForestIndex V, I.cubeContribution ρ :=
        Equiv.sum_comp indexEquiv (fun I => I.cubeContribution ρ)
end BKARMirror
