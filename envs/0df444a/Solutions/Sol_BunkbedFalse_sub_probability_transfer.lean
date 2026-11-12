-- Prove2me | solution 1 for BunkbedFalse.sub_probability_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T07:08:11.078255+00:00
-- url     : https://prove2.me/submissions/f0a19b81-ad19-4ca5-8273-6c05603bddde

import Theorems.Thm_BunkbedFalse_sub_gadget_copies_disjoint
import Theorems.Thm_BunkbedFalse_sub_probability_grouping

open Bunkbed Bunkbed.Hyper Bunkbed.Sub

theorem solution (P : WZ → ℚ)
    (habc : P .abc = Pabc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hab : P .ab_c = Pab_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hac : P .ac_b = Pac_b (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hbc : P .a_bc = Pa_bc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hsep : P .a_b_c = Pa_b_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (x y : Fin 10) (l : Fin 2) :
    bbProb subEdges (fun _ => (1/2 : ℚ)) subT (iota x, 0) (iota y, l) =
      wzProb hollomTriple hollomT P (x, 0) (y, l) := by
  exact BunkbedFalse.sub_probability_grouping
    BunkbedFalse.sub_gadget_copies_disjoint P habc hab hac hbc hsep x y l
