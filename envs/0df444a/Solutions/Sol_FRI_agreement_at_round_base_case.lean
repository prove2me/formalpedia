-- Prove2me | solution 1 for FRI_agreement_at_round_base_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:32:57.68549+00:00
-- url     : https://prove2.me/submissions/898ad429-aa79-4c31-b74b-604b4eff0d26

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (h_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings) :
    FRI_agreement_at_round P f_0 T (Fin.last P.num_foldings) := by
  -- Show FRI_final_oracle equals FRI_get_val at the last round
  unfold FRI_agreement_at_round
  refine ⟨FRI_final_oracle P f_0 T, ?_, ?_⟩
  · -- Show FRI_final_oracle ∈ FRI_code P P.num_foldings
    exact h_final
  · -- Show FRI_final_oracle agrees with FRI_get_val on the green set
    intro x hx
    have hx_domain : x ∈ FRI_domain P (Fin.last P.num_foldings) :=
      FRI_green_set_subset_domain P f_0 T (Fin.last P.num_foldings) hx
    -- Show FRI_final_oracle agrees with FRI_get_val on domain elements
    unfold FRI_final_oracle FRI_get_val
    by_cases h0 : P.num_foldings = 0 <;> simp only [h0, Fin.last, ↓reduceDIte]
    · -- Case: P.num_foldings = 0
      simp_all only [Fin.last, FRI_domain, ↓reduceDIte]
    · -- Case: P.num_foldings ≠ 0
      simp_all only [Fin.last, ↓reduceDIte]
