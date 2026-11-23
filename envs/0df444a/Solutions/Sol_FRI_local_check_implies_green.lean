-- Prove2me | solution 1 for FRI_local_check_implies_green
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:32:28.649814+00:00
-- url     : https://prove2.me/submissions/d8e1d890-d550-46da-aa62-2868218e9172

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (s : F)
    (h_local : ∀ i : Fin P.num_foldings, FRI_local_check P f_0 T s i) :
    FRI_is_green P f_0 T 0 s := by
  have h_induction : ∀ i : ℕ, i ≤ P.num_foldings →
      FRI_is_green P f_0 T i (folded_query P s i) := by
    intro i hi
    induction h : P.num_foldings - i generalizing i with
    | zero => grind [FRI_is_green]
    | succ k ih =>
      have h_lt : i < P.num_foldings := by omega
      have h_fold_check : FRI_fold_check P f_0 T ⟨i, h_lt⟩ (folded_query P s (i + 1)) :=
        h_local ⟨i, h_lt⟩
      grind [FRI_is_green, folded_query]
  exact h_induction 0 bot_le
