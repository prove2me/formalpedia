-- Prove2me | solution 1 for BKAR.Forest.pathMin_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:27.873804+00:00
-- url     : https://prove2.me/submissions/353347fa-fed6-4a65-af96-80cbdf9d3850

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    (e : Edge V) (γ : List (Edge V)) :
    F.pathMin u (e :: γ) = F.pathMinAux u (F.paramValue u e) γ :=
  rfl
end BKAR.Forest
