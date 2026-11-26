-- Prove2me | solution 1 for BKAR.Forest.activeEdgePartialSum_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:46.3828+00:00
-- url     : https://prove2.me/submissions/ab90a29c-f683-41b1-9f69-e6432383f5e4

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    F.activeEdgePartialSum u ρ t =
      Finset.sum F.activeEdges
        (fun e => partialDeriv e ρ (F.interpWithFill u t)) :=
  rfl
end BKAR.Forest
