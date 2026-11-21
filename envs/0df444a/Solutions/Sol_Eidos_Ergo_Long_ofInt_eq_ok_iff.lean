-- Prove2me | solution 1 for Eidos.Ergo.Long.ofInt_eq_ok_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:36:14.848686+00:00
-- url     : https://prove2.me/submissions/a2b6c75e-611b-4919-a9e0-44a43b6b339a

import Std
import Definitions.Def_Eidos_Ergo_Long

set_option autoImplicit false
open Eidos Eidos.Ergo
open Eidos.Ergo.Long
namespace Eidos.Ergo.Long
theorem _root_.solution (n : Int) (x : Long) :
    ofInt n = .ok x ↔ n = x.val := by
  unfold ofInt
  split
  · simp only [Except.ok.injEq, Subtype.ext_iff]
  · rename_i h
    constructor
    · intro impossible
      cases impossible
    · intro hn
      exact False.elim (h (hn ▸ x.property))
end Eidos.Ergo.Long
