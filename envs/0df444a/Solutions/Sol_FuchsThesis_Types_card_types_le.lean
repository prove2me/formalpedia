-- Prove2me | solution 1 for FuchsThesis.Types.card_types_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:02:57.352489+00:00
-- url     : https://prove2.me/submissions/13cb45e7-a81f-4c6b-97dd-c2c58469fdcd

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types

set_option autoImplicit false

open ModernOnlineLearning.Portfolio

theorem solution (B n : ℕ) (hn : 1 ≤ n) :
    (possibleTypes B n).encard ≤ (((n + 1) ^ B : ℕ) : ℕ∞) := by
  have hsub : possibleTypes B n ⊆
      Set.range (fun c : Fin B → Fin (n + 1) => fun i => ((c i : ℕ) : ℝ) / (n : ℝ)) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨fun i => ⟨(Finset.univ.filter (fun t : Fin n => j t = i)).card,
      Nat.lt_succ_of_le (le_trans (Finset.card_filter_le _ _) (by simp))⟩, ?_⟩
    funext i
    simp [sequenceType]
  calc (possibleTypes B n).encard
      ≤ (Set.range (fun c : Fin B → Fin (n + 1) => fun i => ((c i : ℕ) : ℝ) / (n : ℝ))).encard :=
        Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (Fin B → Fin (n + 1))).encard := by
        rw [← Set.image_univ]; exact Set.encard_image_le _ _
    _ = (((n + 1) ^ B : ℕ) : ℕ∞) := by
        rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
        simp
