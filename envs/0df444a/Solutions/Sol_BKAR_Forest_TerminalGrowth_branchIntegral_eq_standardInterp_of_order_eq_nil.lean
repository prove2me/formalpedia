-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.branchIntegral_eq_standardInterp_of_order_eq_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:03.145023+00:00
-- url     : https://prove2.me/submissions/80e7fb35-7d36-46a1-a7f8-fdc45a1f4a18

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_eq_standardInterp_of_order_eq_nil

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth F) (horder : data.order = [])
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = ρ (F.standardInterp u) :=
  data.branchIntegralAux_eq_standardInterp_of_order_eq_nil horder 1 u ρ
end BKAR.Forest.TerminalGrowth
