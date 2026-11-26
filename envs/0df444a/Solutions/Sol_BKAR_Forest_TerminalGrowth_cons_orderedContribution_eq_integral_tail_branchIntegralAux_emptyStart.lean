-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.cons_orderedContribution_eq_integral_tail_branchIntegralAux_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:08.379219+00:00
-- url     : https://prove2.me/submissions/b8b46457-3b16-4783-852b-094d77ba7923

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_TerminalGrowth_cons_branchIntegral_eq_integral_tail_partialDeriv
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    {e : Edge V} (h : ActiveExtension (Forest.empty V) e)
    (tail : TerminalGrowth h.forest) (ρ : (Edge V → ℝ) → ℝ) :
    tail.terminal.orderedContribution (e :: tail.order) ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam emptyParam t)
          (partialDeriv e ρ) := by
  change
    (TerminalGrowth.cons h tail).terminal.orderedContribution
        (TerminalGrowth.cons h tail).order ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam emptyParam t)
          (partialDeriv e ρ)
  rw [← (TerminalGrowth.cons h tail).branchIntegral_emptyStart_eq_orderedContribution ρ]
  rw [TerminalGrowth.cons_branchIntegral_eq_integral_tail_partialDeriv
    h tail emptyParam ρ]
end BKAR.Forest.TerminalGrowth
