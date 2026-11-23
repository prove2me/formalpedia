-- Prove2me | solution 1 for FRI_card_bad_query_sequences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:33:50.21022+00:00
-- url     : https://prove2.me/submissions/6fcb6fde-957e-4c66-92ef-428f873dc991

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) :
    (Finset.univ.filter (fun s : Fin P.q_rep → { x // x ∈ P.D_0 } ↦
      ∀ j : Fin P.q_rep, (s j).val ∈ FRI_W P f_0 T 0)).card =
    (FRI_W P f_0 T 0).card ^ P.q_rep := by
  simp only [FRI_W, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    Subtype.coe_eta, Finset.coe_mem, exists_const]
  -- The set of sequences s where each element is in W0 is equivalent to the set of functions
  -- from Fin P.q_rep to W0.
  have h_equiv : {s : Fin P.q_rep → {x : F // x ∈ P.D_0} | ∀ j, s j ∈ FRI_BadQuery_Points P f_0 T}
      ≃ (Fin P.q_rep → FRI_BadQuery_Points P f_0 T) :=
    ⟨fun s j ↦ ⟨s.1 j, s.2 j⟩,
      fun s ↦ ⟨fun j ↦ (s j).1, fun j ↦ (s j).2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  rw [Finset.card_image_of_injective _ Subtype.coe_injective]
  convert Fintype.card_congr h_equiv
  · rw [← Fintype.subtype_card]
  · simp only [Fintype.card_pi_const, Fintype.card_coe]
