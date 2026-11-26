-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.branchIntegral_eq_branchIntegralAux_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:43.820799+00:00
-- url     : https://prove2.me/submissions/bfc6617c-6f84-4bab-87bd-3d0f49304fa1

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = data.branchIntegralAux 1 u ρ :=
  rfl
end BKAR.Forest.TerminalGrowth
