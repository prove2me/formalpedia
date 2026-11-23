-- Prove2me | solution 1 for FRI_query_prob_le_W0_ratio_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:38:06.881851+00:00
-- url     : https://prove2.me/submissions/98bc7029-5499-42ae-88c7-62200567becb

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_card_bad_query_sequences
import Theorems.Thm_FRI_query_prob_eq_card_div
import Theorems.Thm_FRI_accepting_set_eq_bad_query_sequences
import Theorems.Thm_FRI_D0_nonempty


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_pass : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_nonempty : Nonempty { x // x ∈ P.D_0 }) :
    FRI_query_prob P f_0 bound T ≤
    ENNReal.ofReal ((((FRI_W P f_0 T 0).card : ℝ) / (P.D_0.card : ℝ)) ^ P.q_rep) := by
  rw [FRI_query_prob_eq_card_div P f_0 bound T h_nonempty]
  have h_eq := FRI_accepting_set_eq_bad_query_sequences P f_0 bound T h_state h_pass
  classical
  have h_filter_eq : (Finset.univ.filter (fun s : Fin P.q_rep → { x // x ∈ P.D_0 } ↦
      let T' := { T with s := s }
      FRI_State P f_0 bound T' (P.num_foldings + 1))) =
    (Finset.univ.filter (fun s : Fin P.q_rep → { x // x ∈ P.D_0 } ↦
      ∀ j : Fin P.q_rep, (s j).val ∈ FRI_W P f_0 T 0)) :=
    Finset.filter_congr fun s _ ↦ Set.ext_iff.mp h_eq s
  rw [h_filter_eq]
  simp only [Fintype.card_fun, Fintype.card_coe, FRI_card_bad_query_sequences, Fintype.card_fin]
  have h_eq_real : (((FRI_W P f_0 T 0).card ^ P.q_rep : ℕ) : ℝ) / ((P.D_0.card ^ P.q_rep : ℕ) : ℝ) =
      (((FRI_W P f_0 T 0).card : ℝ) / (P.D_0.card : ℝ)) ^ P.q_rep := by
    rw [Nat.cast_pow, Nat.cast_pow, (div_pow ..).symm]
  rw [ENNReal.le_ofReal_iff_toReal_le]
  · rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, h_eq_real]
  · apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · simp only [ne_eq, Nat.cast_eq_zero, pow_eq_zero_iff']
      intro ⟨h, _⟩
      exact (FRI_D0_nonempty P).ne_empty (Finset.card_eq_zero.mp h)
  · positivity
