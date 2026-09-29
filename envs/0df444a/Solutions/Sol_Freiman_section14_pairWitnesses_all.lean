-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T11:26:42.275363+00:00
-- url     : https://prove2.me/submissions/8077afc2-9286-4e50-9a70-5322dfcdaae7

import Theorems.Thm_Freiman_section14_pairWitnesses_0000_0128
import Theorems.Thm_Freiman_section14_pairWitnesses_0128_0256
import Theorems.Thm_Freiman_section14_pairWitnesses_0256_0384
import Theorems.Thm_Freiman_section14_pairWitnesses_0384_0512
import Theorems.Thm_Freiman_section14_pairWitnesses_0512_0640
import Theorems.Thm_Freiman_section14_pairWitnesses_0640_0768
import Theorems.Thm_Freiman_section14_pairWitnesses_0768_0896
import Theorems.Thm_Freiman_section14_pairWitnesses_0896_1024
import Theorems.Thm_Freiman_section14_pairWitnesses_1024_1152
import Theorems.Thm_Freiman_section14_pairWitnesses_1152_1280
import Theorems.Thm_Freiman_section14_pairWitnesses_1280_1408
import Theorems.Thm_Freiman_section14_pairWitnesses_1408_1536
import Theorems.Thm_Freiman_section14_pairWitnesses_1536_1664
import Theorems.Thm_Freiman_section14_pairWitnesses_1664_1736
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
theorem _root_.solution : ∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  let xs := section14Catalog.assignments
  let P := fun a : Section14Assignment => certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
  have h1736 : ∀ x ∈ xs.drop 1736, P x := by
    apply all_empty P _
    rfl
  have h1664 : ∀ x ∈ xs.drop 1664, P x := by
    apply all_of_chunks P xs 1664 72 (Freiman.section14_pairWitnesses_1664_1736)
    exact h1736
  have h1536 : ∀ x ∈ xs.drop 1536, P x := by
    apply all_of_chunks P xs 1536 128 (Freiman.section14_pairWitnesses_1536_1664)
    exact h1664
  have h1408 : ∀ x ∈ xs.drop 1408, P x := by
    apply all_of_chunks P xs 1408 128 (Freiman.section14_pairWitnesses_1408_1536)
    exact h1536
  have h1280 : ∀ x ∈ xs.drop 1280, P x := by
    apply all_of_chunks P xs 1280 128 (Freiman.section14_pairWitnesses_1280_1408)
    exact h1408
  have h1152 : ∀ x ∈ xs.drop 1152, P x := by
    apply all_of_chunks P xs 1152 128 (Freiman.section14_pairWitnesses_1152_1280)
    exact h1280
  have h1024 : ∀ x ∈ xs.drop 1024, P x := by
    apply all_of_chunks P xs 1024 128 (Freiman.section14_pairWitnesses_1024_1152)
    exact h1152
  have h896 : ∀ x ∈ xs.drop 896, P x := by
    apply all_of_chunks P xs 896 128 (Freiman.section14_pairWitnesses_0896_1024)
    exact h1024
  have h768 : ∀ x ∈ xs.drop 768, P x := by
    apply all_of_chunks P xs 768 128 (Freiman.section14_pairWitnesses_0768_0896)
    exact h896
  have h640 : ∀ x ∈ xs.drop 640, P x := by
    apply all_of_chunks P xs 640 128 (Freiman.section14_pairWitnesses_0640_0768)
    exact h768
  have h512 : ∀ x ∈ xs.drop 512, P x := by
    apply all_of_chunks P xs 512 128 (Freiman.section14_pairWitnesses_0512_0640)
    exact h640
  have h384 : ∀ x ∈ xs.drop 384, P x := by
    apply all_of_chunks P xs 384 128 (Freiman.section14_pairWitnesses_0384_0512)
    exact h512
  have h256 : ∀ x ∈ xs.drop 256, P x := by
    apply all_of_chunks P xs 256 128 (Freiman.section14_pairWitnesses_0256_0384)
    exact h384
  have h128 : ∀ x ∈ xs.drop 128, P x := by
    apply all_of_chunks P xs 128 128 (Freiman.section14_pairWitnesses_0128_0256)
    exact h256
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 128 (Freiman.section14_pairWitnesses_0000_0128)
    exact h128
  simpa only [List.drop_zero] using h0

#print axioms solution
