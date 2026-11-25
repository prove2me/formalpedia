-- Prove2me | solution 1 for ConjCoord.Proof.reps_eq_cntL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:42.126728+00:00
-- url     : https://prove2.me/submissions/49bc057d-c017-4bda-995a-22eeec9f8474

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute
public import Theorems.Thm_ConjCoord_Proof_count_eq_cntL

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (a b c n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    reps a b c n = cntL a b c n (fun _ _ => true) := by
  rw [← count_eq_cntL a b c n ha hb hc (fun _ _ => True) _ (fun _ _ => by simp)]
  unfold reps
  congr 1
  exact filter_congr fun v _ => by simp
end ConjCoord.Proof
