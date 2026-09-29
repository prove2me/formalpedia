-- Prove2me | solution 1 for Freiman.lower_family_root
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:06.809689+00:00
-- url     : https://prove2.me/submissions/2a5f39b3-cd30-4238-98de-bf86bdfa751e

import Theorems.Thm_Freiman_lower_marked_entry_transfer
import Theorems.Thm_Freiman_lower_six_entry_geometry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (ht : ∃ (f : LowerInitialFamily) (n k p : ℕ), t ∈ lowerFamilyH f n k p) :
    ∃ r : LowerPair, lowerInitialRoot t r ∧ lowerState t r := by
  classical
  by_cases hb : ∃ n k p, t ∈ lowerFamilyH .B n k p
  · rcases hb with ⟨n,k,p,h⟩
    exact lower_marked_entry_transfer lower_six_entry_geometry t .B n k p ⟨h,Or.inl rfl⟩
  · rcases ht with ⟨f,n,k,p,h⟩
    exact lower_marked_entry_transfer lower_six_entry_geometry t f n k p ⟨h,Or.inr hb⟩
