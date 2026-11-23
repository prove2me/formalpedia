-- Prove2me | solution 1 for Folding_implies_BadEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:41:58.004325+00:00
-- url     : https://prove2.me/submissions/2055bfce-c47b-492b-8c2f-6621e089d5c0

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Theorems.Thm_folding_event_implies_bad_event

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0) (hd : d ≥ m)
    (f : F → F) (delta : ℝ) (r : F)
    (h_event : FoldingBadEvent D m (reedSolomon D d)
      (reedSolomon (pow_domain D m) (d / m)) f delta r) :
    let L := pow_domain D m
    let C1 := reedSolomon L (d / m)
    let f_i := folding_components D m f
    let vec_r := fun i : Fin m ↦ r ^ (i : ℕ)
    BadEvent C1 m f_i delta vec_r :=
  folding_event_implies_bad_event _ _ _ hm hd _ _ _ h_event
