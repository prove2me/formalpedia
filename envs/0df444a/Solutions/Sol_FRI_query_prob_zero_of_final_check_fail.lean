-- Prove2me | solution 1 for FRI_query_prob_zero_of_final_check_fail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:35:32.222386+00:00
-- url     : https://prove2.me/submissions/a98d53a2-52c7-49b6-913f-5ea070110863

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_State_independent_of_s
import Theorems.Thm_FRI_State_succ_iff_verifier_accepts

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution [Fintype F] [MeasurableSpace F]
    [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_fail : FRI_final_oracle P f_0 T ∉ FRI_code P P.num_foldings) :
    FRI_query_prob P f_0 bound T = 0 := by
  simp only [FRI_query_prob]
  split_ifs <;> simp_all only [PMF.toMeasure_apply_fintype, Finset.sum_eq_zero_iff,
    Finset.mem_univ, Set.indicator_apply_eq_zero, Set.mem_setOf_eq, PMF.uniformOfFintype_apply,
    Fintype.card_pi, Fintype.card_coe, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, imp_false, forall_const, nonempty_subtype,
    not_exists]
  intro s hs
  rw [FRI_State_succ_iff_verifier_accepts P f_0 bound] at hs
  · exact h_fail hs.1
  · exact mt (FRI_State_independent_of_s P f_0 bound T.f T.alpha s T.s P.num_foldings
      (le_refl _)).mp h_state
