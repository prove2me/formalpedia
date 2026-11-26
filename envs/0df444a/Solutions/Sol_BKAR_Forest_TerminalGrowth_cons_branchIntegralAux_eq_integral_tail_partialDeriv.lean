-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.cons_branchIntegralAux_eq_integral_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:55:49.645441+00:00
-- url     : https://prove2.me/submissions/9e888640-1ba3-48c2-ab30-318b26b1349b

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
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
    (tail : TerminalGrowth h.forest) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (cons h tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) :=
  h.consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
    tail.growth top u ρ
end BKAR.Forest.TerminalGrowth
