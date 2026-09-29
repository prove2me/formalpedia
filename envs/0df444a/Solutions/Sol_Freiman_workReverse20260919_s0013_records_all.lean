-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T10:08:55.479519+00:00
-- url     : https://prove2.me/submissions/2eeabc6a-f3ad-4bcc-a8c0-f53bb4ee6199

import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0000_0064
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0064_0320
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0320_0576
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0576_0704
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0704_0960
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0960_1088
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_1088_1216
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_1216_1344
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_1344_1472
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_1472_1600
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_1600_1728
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_1728_1856
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_1856_1984
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_1984_2112
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_2112_2240
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_2240_2368
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_2368_2496
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_2496_2592
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_2592_2688
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_2688_2816
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_2816_2901
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

namespace WorkReverseBundleStandalone_9ec964fec444e871409e
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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (13 ∈ r.states))), section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  have h2901 : ∀ x ∈ xs.drop 2901, P x := by
    apply all_empty P _
    rfl
  have h2816 : ∀ x ∈ xs.drop 2816, P x := by
    apply all_of_chunks P xs 2816 85 (Freiman.workReverse20260919_s0013_records_2816_2901 hnum)
    exact h2901
  have h2688 : ∀ x ∈ xs.drop 2688, P x := by
    apply all_of_chunks P xs 2688 128 (Freiman.workReverse20260919_s0013_records_2688_2816 hnum)
    exact h2816
  have h2592 : ∀ x ∈ xs.drop 2592, P x := by
    apply all_of_chunks P xs 2592 96 (Freiman.workReverse20260919_s0013_records_2592_2688 hnum)
    exact h2688
  have h2496 : ∀ x ∈ xs.drop 2496, P x := by
    apply all_of_chunks P xs 2496 96 (Freiman.workReverse20260919_s0013_records_2496_2592 hnum)
    exact h2592
  have h2368 : ∀ x ∈ xs.drop 2368, P x := by
    apply all_of_chunks P xs 2368 128 (Freiman.workReverse20260919_s0013_records_2368_2496 hnum)
    exact h2496
  have h2240 : ∀ x ∈ xs.drop 2240, P x := by
    apply all_of_chunks P xs 2240 128 (Freiman.workReverse20260919_s0013_records_2240_2368 hnum)
    exact h2368
  have h2112 : ∀ x ∈ xs.drop 2112, P x := by
    apply all_of_chunks P xs 2112 128 (Freiman.workReverse20260919_s0013_records_2112_2240 hnum)
    exact h2240
  have h1984 : ∀ x ∈ xs.drop 1984, P x := by
    apply all_of_chunks P xs 1984 128 (Freiman.workReverse20260919_s0013_records_1984_2112 hnum)
    exact h2112
  have h1856 : ∀ x ∈ xs.drop 1856, P x := by
    apply all_of_chunks P xs 1856 128 (Freiman.workReverse20260919_s0013_records_1856_1984 hnum)
    exact h1984
  have h1728 : ∀ x ∈ xs.drop 1728, P x := by
    apply all_of_chunks P xs 1728 128 (Freiman.workReverse20260919_s0013_records_1728_1856 hnum)
    exact h1856
  have h1600 : ∀ x ∈ xs.drop 1600, P x := by
    apply all_of_chunks P xs 1600 128 (Freiman.workReverse20260919_s0013_records_1600_1728 hnum)
    exact h1728
  have h1472 : ∀ x ∈ xs.drop 1472, P x := by
    apply all_of_chunks P xs 1472 128 (Freiman.workReverse20260919_s0013_records_1472_1600 hnum)
    exact h1600
  have h1344 : ∀ x ∈ xs.drop 1344, P x := by
    apply all_of_chunks P xs 1344 128 (Freiman.workReverse20260919_s0013_records_1344_1472 hnum)
    exact h1472
  have h1216 : ∀ x ∈ xs.drop 1216, P x := by
    apply all_of_chunks P xs 1216 128 (Freiman.workReverse20260919_s0013_records_1216_1344 hnum)
    exact h1344
  have h1088 : ∀ x ∈ xs.drop 1088, P x := by
    apply all_of_chunks P xs 1088 128 (Freiman.workReverse20260919_s0013_records_1088_1216 hnum)
    exact h1216
  have h960 : ∀ x ∈ xs.drop 960, P x := by
    apply all_of_chunks P xs 960 128 (Freiman.workReverse20260919_s0013_records_0960_1088 hnum)
    exact h1088
  have h704 : ∀ x ∈ xs.drop 704, P x := by
    apply all_of_chunks P xs 704 256 (Freiman.workReverse20260919_s0013_records_0704_0960 hnum)
    exact h960
  have h576 : ∀ x ∈ xs.drop 576, P x := by
    apply all_of_chunks P xs 576 128 (Freiman.workReverse20260919_s0013_records_0576_0704 hnum)
    exact h704
  have h320 : ∀ x ∈ xs.drop 320, P x := by
    apply all_of_chunks P xs 320 256 (Freiman.workReverse20260919_s0013_records_0320_0576 hnum)
    exact h576
  have h64 : ∀ x ∈ xs.drop 64, P x := by
    apply all_of_chunks P xs 64 256 (Freiman.workReverse20260919_s0013_records_0064_0320 hnum)
    exact h320
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 64 (Freiman.workReverse20260919_s0013_records_0000_0064 hnum)
    exact h64
  simpa only [List.drop_zero] using h0

end WorkReverseBundleStandalone_9ec964fec444e871409e

#print axioms solution
