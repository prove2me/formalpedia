-- Prove2me | solution 1 for Erdos266.blk_close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:02:45.326266+00:00
-- url     : https://prove2.me/submissions/2d63d226-a154-4a74-b754-bed8baba4641

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
    ∀ i : Fin (dOf k),
      |Xvec k st i - ∑ j : Fin (dOf k),
          f (i.val + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ))|
        ≤ DL (dOf k) * (1 / (bigN k : ℝ) ^ (i.val + 2)
            + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i.val + 3)) :=
  (latt (dOf k) (bigN k) (bigM k) (one_le_bigN k) (four_dOf_le k)
    (Xvec k st) (step_hyp h)).choose_spec.2
end Erdos266
