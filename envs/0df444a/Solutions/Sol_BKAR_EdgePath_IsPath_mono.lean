-- Prove2me | solution 1 for BKAR.EdgePath.IsPath.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:22.070974+00:00
-- url     : https://prove2.me/submissions/f859943c-6edd-47ec-9b7f-1fc2f4dbf16d

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.EdgePath
variable {V} [DecidableEq V]
open BKAR.EdgePath.IsPath
namespace BKAR.EdgePath.IsPath
theorem _root_.solution {S T : Finset (Edge V)} (hsub : S ⊆ T) :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j → IsPath T γ i j
  | [], _i, _j, h => by
      cases h
      exact IsPath.nil _
  | _e :: _γ, _i, _j, h => by
      cases h with
      | cons he hbetween htail =>
          exact IsPath.cons (hsub he) hbetween (solution hsub htail)
end BKAR.EdgePath.IsPath
