-- Prove2me | solution 1 for Freiman.section14_s0014_coverage0007_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:14:13.727389+00:00
-- url     : https://prove2.me/submissions/8c16e16e-41a4-43e1-89d1-17b0859d3b24

import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0000_0016
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0016_0032
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0032_0048
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0048_0064
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0064_0080
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0080_0096
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0096_0112
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0112_0128
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0128_0144
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0144_0160
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0160_0176
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0176_0192
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0192_0208
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0208_0224
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0224_0240
import Theorems.Thm_Freiman_section14_s0014_coverage0007_parents_0240_0256
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
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 7).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 14), section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j := by
  intro pl hpl
  let xs := section14Parents section14Catalog (section14State section14Catalog 14)
  let P := fun b : Section14Parent => section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j
  have h256 : ∀ x ∈ xs.drop 256, P x := by
    apply all_empty P _
    rfl
  have h240 : ∀ x ∈ xs.drop 240, P x := by
    apply all_of_chunks P xs 240 16 (Freiman.section14_s0014_coverage0007_parents_0240_0256 pl hpl)
    exact h256
  have h224 : ∀ x ∈ xs.drop 224, P x := by
    apply all_of_chunks P xs 224 16 (Freiman.section14_s0014_coverage0007_parents_0224_0240 pl hpl)
    exact h240
  have h208 : ∀ x ∈ xs.drop 208, P x := by
    apply all_of_chunks P xs 208 16 (Freiman.section14_s0014_coverage0007_parents_0208_0224 pl hpl)
    exact h224
  have h192 : ∀ x ∈ xs.drop 192, P x := by
    apply all_of_chunks P xs 192 16 (Freiman.section14_s0014_coverage0007_parents_0192_0208 pl hpl)
    exact h208
  have h176 : ∀ x ∈ xs.drop 176, P x := by
    apply all_of_chunks P xs 176 16 (Freiman.section14_s0014_coverage0007_parents_0176_0192 pl hpl)
    exact h192
  have h160 : ∀ x ∈ xs.drop 160, P x := by
    apply all_of_chunks P xs 160 16 (Freiman.section14_s0014_coverage0007_parents_0160_0176 pl hpl)
    exact h176
  have h144 : ∀ x ∈ xs.drop 144, P x := by
    apply all_of_chunks P xs 144 16 (Freiman.section14_s0014_coverage0007_parents_0144_0160 pl hpl)
    exact h160
  have h128 : ∀ x ∈ xs.drop 128, P x := by
    apply all_of_chunks P xs 128 16 (Freiman.section14_s0014_coverage0007_parents_0128_0144 pl hpl)
    exact h144
  have h112 : ∀ x ∈ xs.drop 112, P x := by
    apply all_of_chunks P xs 112 16 (Freiman.section14_s0014_coverage0007_parents_0112_0128 pl hpl)
    exact h128
  have h96 : ∀ x ∈ xs.drop 96, P x := by
    apply all_of_chunks P xs 96 16 (Freiman.section14_s0014_coverage0007_parents_0096_0112 pl hpl)
    exact h112
  have h80 : ∀ x ∈ xs.drop 80, P x := by
    apply all_of_chunks P xs 80 16 (Freiman.section14_s0014_coverage0007_parents_0080_0096 pl hpl)
    exact h96
  have h64 : ∀ x ∈ xs.drop 64, P x := by
    apply all_of_chunks P xs 64 16 (Freiman.section14_s0014_coverage0007_parents_0064_0080 pl hpl)
    exact h80
  have h48 : ∀ x ∈ xs.drop 48, P x := by
    apply all_of_chunks P xs 48 16 (Freiman.section14_s0014_coverage0007_parents_0048_0064 pl hpl)
    exact h64
  have h32 : ∀ x ∈ xs.drop 32, P x := by
    apply all_of_chunks P xs 32 16 (Freiman.section14_s0014_coverage0007_parents_0032_0048 pl hpl)
    exact h48
  have h16 : ∀ x ∈ xs.drop 16, P x := by
    apply all_of_chunks P xs 16 16 (Freiman.section14_s0014_coverage0007_parents_0016_0032 pl hpl)
    exact h32
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 16 (Freiman.section14_s0014_coverage0007_parents_0000_0016 pl hpl)
    exact h16
  simpa only [List.drop_zero] using h0

#print axioms solution
