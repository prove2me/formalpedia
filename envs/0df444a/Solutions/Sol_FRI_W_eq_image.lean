-- Prove2me | solution 1 for FRI_W_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:25:41.965069+00:00
-- url     : https://prove2.me/submissions/58283e41-b22e-40da-b566-aed13cb3383c

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) (h : i ≤ P.num_foldings) :
    FRI_W P f_0 T i = (FRI_W P f_0 T 0).image (fun s ↦ folded_query P s i) := by
  induction i with
  | zero => simp [folded_query]
  | succ i ih =>
    simp only [FRI_W, dif_pos (by grind : i < P.num_foldings), pow_domain,
      ih (Nat.le_of_succ_le h), Finset.image_image, Finset.ext_iff, Finset.mem_image,
      Function.comp_apply, folded_query, forall_const]
