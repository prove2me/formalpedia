-- Prove2me | solution 1 for Erdos266.stepSt_fst_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:03:22.952546+00:00
-- url     : https://prove2.me/submissions/a16cd281-1b9e-418e-bf87-59a2d33ff291

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_newS_eq_of_lt
public import Theorems.Thm_Erdos266_stepSt_eq


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {k : ℕ} {st : AlgSt} (h : Inv k st) {l : ℕ} (hl : l ≠ k) (j : ℕ) :
    (stepSt k st).1 l j = st.1 l j := by
  rw [stepSt_eq h]
  exact newS_eq_of_lt h hl j
end Erdos266
