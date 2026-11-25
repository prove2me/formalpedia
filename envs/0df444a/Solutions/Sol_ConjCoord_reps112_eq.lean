-- Prove2me | solution 1 for ConjCoord.reps112_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:18.753088+00:00
-- url     : https://prove2.me/submissions/3f2167fa-b42e-4db5-a861-e1e613d82b89

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_reps112_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution {n : ℕ} (hn : n % 2 = 1) : reps 1 1 2 n = 2 * reps 1 2 4 n :=
  Proof.reps112_eq hn
end ConjCoord
