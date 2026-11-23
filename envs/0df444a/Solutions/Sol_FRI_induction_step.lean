-- Prove2me | solution 1 for FRI_induction_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:26:08.201453+00:00
-- url     : https://prove2.me/submissions/7edcacbb-0b18-47e7-baff-98e1a3e4676a

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (i : Fin P.num_foldings)
    (h_large : FRI_Is_Large_Subset P f_0 bound i i.isLt (FRI_W P f_0 T i))
    (u_next : FRI_domain P (i + 1) → F)
    (h_u_next_in_code : u_next ∈ FRI_code P (i + 1))
    (h_agree_next : ∀ z ∈ FRI_W P f_0 T (i + 1),
        Fold (FRI_domain P i) (P.m i)
          (extend_by_zero (FRI_domain P i) (FRI_oracle_at_round P f_0 T i i.isLt))
          (T.alpha i) z =
        extend_by_zero (FRI_domain P (i + 1)) u_next z)
    (h_no_bad : ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i)) :
    ∃ u_curr ∈ FRI_code P i, ∀ x ∈ FRI_W P f_0 T i,
        extend_by_zero (FRI_domain P i) (FRI_oracle_at_round P f_0 T i i.isLt) x =
        extend_by_zero (FRI_domain P i) u_curr x := by
  simp_all only [FRI_BadEvent, FRI_Is_Large_Subset, not_forall,
    not_exists, not_and, Decidable.not_not, forall_exists_index, and_imp]
  contrapose! h_no_bad
  refine ⟨FRI_W P f_0 T i, h_large.1, h_large.2, u_next, h_u_next_in_code, ?_, ?_⟩
  · simpa only [FRI_W, Fin.is_lt, ↓reduceDIte] using h_agree_next
  · exact h_no_bad
