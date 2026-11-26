-- Prove2me | solution 1 for Erdos266.blk_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:02:42.243543+00:00
-- url     : https://prove2.me/submissions/0d87653a-53ba-47ca-9262-399e5e5024ea

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
public import Theorems.Thm_Erdos266_latt
public import Theorems.Thm_Erdos266_one_le_bigN


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} {st : AlgSt} (h : Inv k st) :
    ∀ j, |blk k st h j| ≤ (bigM k : ℤ) :=
  (latt (dOf k) (bigN k) (bigM k) (one_le_bigN k) (four_dOf_le k)
    (Xvec k st) (step_hyp h)).choose_spec.1
end Erdos266
