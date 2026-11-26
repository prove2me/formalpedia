-- Prove2me | solution 1 for BKAR.Forest.pathMinAux_le_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:31.694708+00:00
-- url     : https://prove2.me/submissions/fc5e07d8-3acc-4341-9191-166192424b7f

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ) :
    ∀ (a : ℝ) (γ : List (Edge V)), F.pathMinAux u a γ ≤ a
  | _, [] => le_rfl
  | a, e :: γ =>
      (solution F u (min a (F.paramValue u e)) γ).trans
        (min_le_left _ _)
end BKAR.Forest
