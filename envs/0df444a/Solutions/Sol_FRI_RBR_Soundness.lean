-- Prove2me | solution 1 for FRI_RBR_Soundness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:44:04.744601+00:00
-- url     : https://prove2.me/submissions/69a5330c-4d40-43da-86c1-a6683959c490

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
import Theorems.Thm_FRI_State_empty_transcript
import Theorems.Thm_FRI_State_Transition_Prob_Fold_eq
import Theorems.Thm_FRI_State_Transition_Prob_Query_eq
import Theorems.Thm_FRI_Domain_Size_Property_of_foldable
import Theorems.Thm_FRI_degree_ge_m
import Theorems.Thm_FRI_distance_star_nonneg
import Theorems.Thm_FRI_domain_card_pos
import Theorems.Thm_FRI_domain_foldable
import Theorems.Thm_FRI_folding_soundness
import Theorems.Thm_FRI_query_soundness


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
theorem _root_.solution
    (P : FRIParameters F)
    (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (h_mca : FRI_MCA_Hypothesis P bound errorstar)
    (h_bound_valid : bound + 1 / P.D_0.card ≤ 1)
    (f_0 : P.D_0 → F) :
    -- Part 0: Initial State (Round 0)
    -- State(f_0, ∅) = 1 iff f_0 ∈ C_0
    (∀ T : FRITranscript P, FRI_State P f_0 bound T 0 ↔ f_0 ∈ (FRI_code P 0).carrier)
    ∧
    -- Part 1: Folding rounds (Rounds 1 to k)
    -- Pr[State(T, i) = 0 ∧ State(T || α, i+1) = 1] ≤ ε^fold_i(δ*)
    -- Note: IsFoldable and FRI_degree ≥ m are derived from FRIParameters
    (∀ T : FRITranscript P,
      ∀ i : Fin P.num_foldings,
      FRI_distance_star P f_0 bound < 1 - bound →
      0 ≤ FRI_error_fold P bound errorstar i (FRI_distance_star P f_0 bound) →
      FRI_State_Transition_Prob_Fold P f_0 bound T i ≤
        FRI_error_fold P bound errorstar i (FRI_distance_star P f_0 bound))
    ∧
    -- Part 2: Query round (Round k+1)
    -- Pr[State(T, k) = 0 ∧ State(T || s, k+1) = 1] ≤ (1 - δ*)^t
    -- Note: f_0 is now a separate parameter, not part of the transcript
    (∀ T : FRITranscript P,
      FRI_State_Transition_Prob_Query P f_0 bound T ≤
        ENNReal.ofReal ((1 - FRI_distance_star P f_0 bound) ^ P.q_rep)) := by
  -- Derive the properties from the FRI parameters
  have h_domain_size := FRI_Domain_Size_Property_of_foldable P
  have h_delta_star_nonneg := FRI_distance_star_nonneg P f_0 bound h_bound_valid
  and_intros
  -- Part 0: Initial State
  · exact FRI_State_empty_transcript P f_0 bound
  -- Part 1: Folding soundness (using State transition probability)
  · intro T i h_delta_lt h_error_nonneg
    -- Case split on whether State(i) = 1 or State(i) = 0
    by_cases h_state : FRI_State P f_0 bound T i
    · -- If State(i) = 1, the transition probability is 0
      grind [FRI_State_Transition_Prob_Fold]
    · -- If State(i) = 0, use the folding soundness lemma
      exact FRI_State_Transition_Prob_Fold_eq P f_0 bound T i h_state ▸
        FRI_folding_soundness P bound errorstar h_mca f_0 i
          (FRI_oracle_at_round P f_0 T i i.isLt) (FRI_degree_ge_m P i) (FRI_domain_foldable P i)
          h_delta_star_nonneg h_delta_lt h_error_nonneg
  -- Part 2: Query soundness (using State transition probability)
  · intro T
    -- Case split on whether State(k) = 1 or State(k) = 0
    by_cases h_state : FRI_State P f_0 bound T P.num_foldings
    · -- If State(k) = 1, the transition probability is 0
      simp [FRI_State_Transition_Prob_Query, h_state]
    · -- If State(k) = 0, use the query soundness lemma
      exact FRI_State_Transition_Prob_Query_eq P f_0 bound T h_state ▸
        FRI_query_soundness P f_0 bound T h_state h_domain_size (FRI_domain_card_pos P)
