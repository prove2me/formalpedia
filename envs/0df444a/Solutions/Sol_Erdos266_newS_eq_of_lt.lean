-- Prove2me | solution 1 for Erdos266.newS_eq_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:55:43.669906+00:00
-- url     : https://prove2.me/submissions/1b7550bb-65be-4a69-8ca7-5681658006e6

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} {st : AlgSt} (h : Inv k st) {l : ℕ} (hl : l ≠ k) (j : ℕ) :
    newS k st h l j = st.1 l j := by
  rw [newS, if_neg hl]
end Erdos266
