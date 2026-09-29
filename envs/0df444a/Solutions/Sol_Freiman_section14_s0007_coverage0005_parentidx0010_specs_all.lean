-- Prove2me | solution 1 for Freiman.section14_s0007_coverage0005_parentidx0010_specs_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:48:10.367433+00:00
-- url     : https://prove2.me/submissions/42951ce2-1c8c-4d34-883b-a918c1a82792

import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0000_0008
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0008_0016
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0016_0024
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0024_0032
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0032_0040
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0040_0048
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0048_0056
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0056_0064
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0064_0072
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0072_0080
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0080_0088
import Theorems.Thm_Freiman_section14_s0007_coverage0005_parentidx0010_specs_0088_0091
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
theorem _root_.solution : ∀ gs ∈ ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 10 gs.1 j := by
  let xs := ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs
  let P := fun gs : ℕ × Section14Spec => ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 10 gs.1 j
  have h91 : ∀ x ∈ xs.drop 91, P x := by
    apply all_empty P _
    rfl
  have h88 : ∀ x ∈ xs.drop 88, P x := by
    apply all_of_chunks P xs 88 3 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0088_0091)
    exact h91
  have h80 : ∀ x ∈ xs.drop 80, P x := by
    apply all_of_chunks P xs 80 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0080_0088)
    exact h88
  have h72 : ∀ x ∈ xs.drop 72, P x := by
    apply all_of_chunks P xs 72 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0072_0080)
    exact h80
  have h64 : ∀ x ∈ xs.drop 64, P x := by
    apply all_of_chunks P xs 64 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0064_0072)
    exact h72
  have h56 : ∀ x ∈ xs.drop 56, P x := by
    apply all_of_chunks P xs 56 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0056_0064)
    exact h64
  have h48 : ∀ x ∈ xs.drop 48, P x := by
    apply all_of_chunks P xs 48 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0048_0056)
    exact h56
  have h40 : ∀ x ∈ xs.drop 40, P x := by
    apply all_of_chunks P xs 40 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0040_0048)
    exact h48
  have h32 : ∀ x ∈ xs.drop 32, P x := by
    apply all_of_chunks P xs 32 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0032_0040)
    exact h40
  have h24 : ∀ x ∈ xs.drop 24, P x := by
    apply all_of_chunks P xs 24 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0024_0032)
    exact h32
  have h16 : ∀ x ∈ xs.drop 16, P x := by
    apply all_of_chunks P xs 16 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0016_0024)
    exact h24
  have h8 : ∀ x ∈ xs.drop 8, P x := by
    apply all_of_chunks P xs 8 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0008_0016)
    exact h16
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 8 (Freiman.section14_s0007_coverage0005_parentidx0010_specs_0000_0008)
    exact h8
  simpa only [List.drop_zero] using h0

#print axioms solution
