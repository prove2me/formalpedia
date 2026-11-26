-- Prove2me | solution 1 for BKAR.EdgePath.IsPath.mono_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:24.585615+00:00
-- url     : https://prove2.me/submissions/82a0dd54-940d-485a-9c68-b48859b8c452

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
theorem _root_.solution {S T : Finset (Edge V)} :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j →
      (∀ e ∈ γ, e ∈ T) →
        IsPath T γ i j
  | [], _i, _j, hpath, _hmem => by
      cases hpath
      exact IsPath.nil _
  | e :: γ, _i, _j, hpath, hmem => by
      cases hpath with
      | cons _he hbetween htail =>
          exact IsPath.cons
            (hmem e (by simp))
            hbetween
            (solution htail
              (fun e' he' => hmem e' (by simp [he'])))
end BKAR.EdgePath.IsPath
