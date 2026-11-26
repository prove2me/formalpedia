-- Prove2me | solution 1 for Erdos266.stepSt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:56:16.534389+00:00
-- url     : https://prove2.me/submissions/2d24b539-7268-4013-8358-dd5d34bc6dae

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
    stepSt k st = (newS k st h,
      if dOf (k + 1) = dOf k + 1
        then Function.update st.2 (dOf k) (newQ k st h)
        else st.2) :=
  dif_pos h
end Erdos266
