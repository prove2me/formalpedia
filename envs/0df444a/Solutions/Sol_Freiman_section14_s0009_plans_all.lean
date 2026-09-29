-- Prove2me | solution 1 for Freiman.section14_s0009_plans_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T22:39:22.220722+00:00
-- url     : https://prove2.me/submissions/d88b865f-b6ff-4805-b0bd-1541879041e8

import Theorems.Thm_Freiman_section14_s0009_plan0000_valid
import Theorems.Thm_Freiman_section14_s0009_plan0001_valid
import Theorems.Thm_Freiman_section14_s0009_plan0002_valid
import Theorems.Thm_Freiman_section14_s0009_plan0003_valid
import Theorems.Thm_Freiman_section14_s0009_plan0004_valid
import Theorems.Thm_Freiman_section14_s0009_plan0005_valid
import Theorems.Thm_Freiman_section14_s0009_plan0006_valid
import Theorems.Thm_Freiman_section14_s0009_plan0007_valid
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

open Freiman
set_option synthInstance.maxSize 100000
set_option maxRecDepth 100000
namespace M7Section14Sep18
instance (r : CertRectangle) : Decidable (certRectangleValid r) := by
  unfold certRectangleValid
  infer_instance
instance (t : CertThreshold) : Decidable (certThresholdDataValid t) := by
  unfold certThresholdDataValid
  infer_instance
instance (z : CertField) (q : ℚ) : Decidable (certCoefficientBoundValid z q) := by
  unfold certCoefficientBoundValid
  infer_instance
instance (w : CertWitness) : Decidable (certWitnessValid w) := by
  unfold certWitnessValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (caseId : ℕ)
    (gs : ℕ × Section14Spec) : Decidable (section14SpecValid C S caseId gs) := by
  unfold section14SpecValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (p : Section14Plan) :
    Decidable (section14PlanValid C S p) := by
  unfold section14PlanValid
  infer_instance
instance (outer inner : CertRectangle) : Decidable (section14RectangleContains outer inner) := by
  unfold section14RectangleContains
  infer_instance
instance (C : Section14Catalog) (si : ℕ) (r : Section14Record) :
    Decidable (section14RecordValid C si r) := by
  unfold section14RecordValid
  infer_instance
instance (C : Section14Catalog) (si parent goal : ℕ) (branch : ℤ) :
    Decidable (section14Recorded C si parent goal branch) := by
  unfold section14Recorded
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14Coverage C si) := by
  unfold section14Coverage
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14StateValid C si) := by
  unfold section14StateValid
  infer_instance
end M7Section14Sep18

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : ∀ p ∈ (section14State section14Catalog 9).plans, section14PlanValid section14Catalog (section14State section14Catalog 9) p := by
  let xs := (section14State section14Catalog 9).plans
  let P := fun p : Section14Plan => section14PlanValid section14Catalog (section14State section14Catalog 9) p
  have h8 : ∀ x ∈ xs.drop 8, P x := by
    apply all_empty P _
    rfl
  have h7 : ∀ x ∈ xs.drop 7, P x := by
    apply all_of_chunks P xs 7 1 (Freiman.section14_s0009_plan0007_valid)
    exact h8
  have h6 : ∀ x ∈ xs.drop 6, P x := by
    apply all_of_chunks P xs 6 1 (Freiman.section14_s0009_plan0006_valid)
    exact h7
  have h5 : ∀ x ∈ xs.drop 5, P x := by
    apply all_of_chunks P xs 5 1 (Freiman.section14_s0009_plan0005_valid)
    exact h6
  have h4 : ∀ x ∈ xs.drop 4, P x := by
    apply all_of_chunks P xs 4 1 (Freiman.section14_s0009_plan0004_valid)
    exact h5
  have h3 : ∀ x ∈ xs.drop 3, P x := by
    apply all_of_chunks P xs 3 1 (Freiman.section14_s0009_plan0003_valid)
    exact h4
  have h2 : ∀ x ∈ xs.drop 2, P x := by
    apply all_of_chunks P xs 2 1 (Freiman.section14_s0009_plan0002_valid)
    exact h3
  have h1 : ∀ x ∈ xs.drop 1, P x := by
    apply all_of_chunks P xs 1 1 (Freiman.section14_s0009_plan0001_valid)
    exact h2
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 1 (Freiman.section14_s0009_plan0000_valid)
    exact h1
  simpa only [List.drop_zero] using h0

#print axioms solution
