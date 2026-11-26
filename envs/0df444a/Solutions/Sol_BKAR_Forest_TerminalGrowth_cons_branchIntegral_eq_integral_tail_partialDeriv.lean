-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.cons_branchIntegral_eq_integral_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:21.383598+00:00
-- url     : https://prove2.me/submissions/29fa55f3-c092-46d7-9ab0-bd70f93663d8

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_cons_branchIntegralAux_eq_integral_tail_partialDeriv
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
    {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (cons h tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) :=
  cons_branchIntegralAux_eq_integral_tail_partialDeriv h tail 1 u ρ
end BKAR.Forest.TerminalGrowth
