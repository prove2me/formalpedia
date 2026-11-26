-- Prove2me | solution 1 for Erdos266.newQ_close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:03:04.481194+00:00
-- url     : https://prove2.me/submissions/9b49d095-1220-44f6-a5f8-fc5bdba800a2

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} {st : AlgSt} (h : Inv k st) :
    |finSum (dOf k) (k + 1) (newS k st h) + tailAnchor (dOf k + 1) (k + 1)
        - (newQ k st h : ℝ)|
      < εA (dOf (k + 1)) * bigM (k + 1) / (bigN (k + 1) : ℝ) ^ (dOf k + 2) :=
  (exists_rat_near
    (finSum (dOf k) (k + 1) (newS k st h) + tailAnchor (dOf k + 1) (k + 1))
    (next_radius_pos h.1 (dOf k))).choose_spec
end Erdos266
