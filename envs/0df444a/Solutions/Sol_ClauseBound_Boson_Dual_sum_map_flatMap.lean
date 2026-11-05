-- Prove2me | solution 1 for ClauseBound.Boson.Dual.sum_map_flatMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:18:20.569989+00:00
-- url     : https://prove2.me/submissions/6800da2c-ebeb-44c6-b474-9e40dbc349f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.Dual
open Finset
namespace ClauseBound.Boson.Dual
theorem _root_.solution {α β : Type} (l : List α) (g : α → List β) (φ : β → ℤ) :
    ((l.flatMap g).map φ).sum = (l.map fun x => ((g x).map φ).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]
end ClauseBound.Boson.Dual
