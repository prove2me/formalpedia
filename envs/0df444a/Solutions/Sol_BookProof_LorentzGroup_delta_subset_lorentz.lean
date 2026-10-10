-- Prove2me | solution 1 for BookProof.LorentzGroup.delta_subset_lorentz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:44:38.482648+00:00
-- url     : https://prove2.me/submissions/22de9638-fda8-49af-909d-a4197868a133

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.delta_subset_lorentz
import Mathlib
import Definitions.Def_ChapterLorentzGroup
import Theorems.Thm_BookProof_LorentzGroup_isLorentz_one
import Theorems.Thm_BookProof_LorentzGroup_isLorentz_eta
import Theorems.Thm_BookProof_LorentzGroup_isLorentz_neg_eta
import Theorems.Thm_BookProof_LorentzGroup_isLorentz_neg_one
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ∀ x ∈ Delta, IsLorentz x := by

  intro x hx; unfold Delta at hx
  rcases hx with ( rfl | rfl | rfl | rfl ) <;>
    [ exact isLorentz_one; exact isLorentz_eta; exact isLorentz_neg_eta;
      exact isLorentz_neg_one ]
