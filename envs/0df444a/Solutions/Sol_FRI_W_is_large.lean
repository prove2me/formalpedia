-- Prove2me | solution 1 for FRI_W_is_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:25:57.536847+00:00
-- url     : https://prove2.me/submissions/9d00a070-6f6c-4968-b3f7-49252fd1c0a9

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_W_subset_domain

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_W_large : ∀ i : Fin (P.num_foldings + 1),
        (FRI_W P f_0 T i).card ≥ (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card)
    (i : Fin P.num_foldings) :
    FRI_Is_Large_Subset P f_0 bound i i.isLt (FRI_W P f_0 T i) := by
  use FRI_W_subset_domain P f_0 T i
  convert h_W_large ⟨i + 1, Nat.succ_lt_succ i.isLt⟩ using 1
  simp only [FRI_W, Fin.eta, Fin.is_lt, ↓reduceDIte]
