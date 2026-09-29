-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:56:00.080567+00:00
-- url     : https://prove2.me/submissions/5a1e803f-9c66-4fa0-9d87-01392b33903a

import Theorems.Thm_Freiman_workReverse20260919_s0001_records_0000_0128
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_0128_0256
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_0256_0384
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_0384_0512
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_0512_0640
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_0640_0768
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_0768_0896
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_0896_1024
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_1024_1152
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_1152_1408
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_1408_1536
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_1536_1664
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_1664_1792
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_1792_1920
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_1920_2048
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_2048_2176
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_2176_2304
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_2304_2432
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_2432_2560
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_2560_2688
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_2688_2816
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_2816_2880
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_2880_3008
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3008_3136
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3136_3200
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3200_3328
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3328_3392
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3392_3456
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3456_3520
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3520_3584
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3584_3648
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3648_3712
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3712_3776
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3776_3904
import Theorems.Thm_Freiman_workReverse20260919_s0001_records_3904_3954
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

namespace WorkReverseBundleStandalone_6ca5f492335faa34debb
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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (1 ∈ r.states))), section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  have h3954 : ∀ x ∈ xs.drop 3954, P x := by
    apply all_empty P _
    rfl
  have h3904 : ∀ x ∈ xs.drop 3904, P x := by
    apply all_of_chunks P xs 3904 50 (Freiman.workReverse20260919_s0001_records_3904_3954 hnum)
    exact h3954
  have h3776 : ∀ x ∈ xs.drop 3776, P x := by
    apply all_of_chunks P xs 3776 128 (Freiman.workReverse20260919_s0001_records_3776_3904 hnum)
    exact h3904
  have h3712 : ∀ x ∈ xs.drop 3712, P x := by
    apply all_of_chunks P xs 3712 64 (Freiman.workReverse20260919_s0001_records_3712_3776 hnum)
    exact h3776
  have h3648 : ∀ x ∈ xs.drop 3648, P x := by
    apply all_of_chunks P xs 3648 64 (Freiman.workReverse20260919_s0001_records_3648_3712 hnum)
    exact h3712
  have h3584 : ∀ x ∈ xs.drop 3584, P x := by
    apply all_of_chunks P xs 3584 64 (Freiman.workReverse20260919_s0001_records_3584_3648 hnum)
    exact h3648
  have h3520 : ∀ x ∈ xs.drop 3520, P x := by
    apply all_of_chunks P xs 3520 64 (Freiman.workReverse20260919_s0001_records_3520_3584 hnum)
    exact h3584
  have h3456 : ∀ x ∈ xs.drop 3456, P x := by
    apply all_of_chunks P xs 3456 64 (Freiman.workReverse20260919_s0001_records_3456_3520 hnum)
    exact h3520
  have h3392 : ∀ x ∈ xs.drop 3392, P x := by
    apply all_of_chunks P xs 3392 64 (Freiman.workReverse20260919_s0001_records_3392_3456 hnum)
    exact h3456
  have h3328 : ∀ x ∈ xs.drop 3328, P x := by
    apply all_of_chunks P xs 3328 64 (Freiman.workReverse20260919_s0001_records_3328_3392 hnum)
    exact h3392
  have h3200 : ∀ x ∈ xs.drop 3200, P x := by
    apply all_of_chunks P xs 3200 128 (Freiman.workReverse20260919_s0001_records_3200_3328 hnum)
    exact h3328
  have h3136 : ∀ x ∈ xs.drop 3136, P x := by
    apply all_of_chunks P xs 3136 64 (Freiman.workReverse20260919_s0001_records_3136_3200 hnum)
    exact h3200
  have h3008 : ∀ x ∈ xs.drop 3008, P x := by
    apply all_of_chunks P xs 3008 128 (Freiman.workReverse20260919_s0001_records_3008_3136 hnum)
    exact h3136
  have h2880 : ∀ x ∈ xs.drop 2880, P x := by
    apply all_of_chunks P xs 2880 128 (Freiman.workReverse20260919_s0001_records_2880_3008 hnum)
    exact h3008
  have h2816 : ∀ x ∈ xs.drop 2816, P x := by
    apply all_of_chunks P xs 2816 64 (Freiman.workReverse20260919_s0001_records_2816_2880 hnum)
    exact h2880
  have h2688 : ∀ x ∈ xs.drop 2688, P x := by
    apply all_of_chunks P xs 2688 128 (Freiman.workReverse20260919_s0001_records_2688_2816 hnum)
    exact h2816
  have h2560 : ∀ x ∈ xs.drop 2560, P x := by
    apply all_of_chunks P xs 2560 128 (Freiman.workReverse20260919_s0001_records_2560_2688 hnum)
    exact h2688
  have h2432 : ∀ x ∈ xs.drop 2432, P x := by
    apply all_of_chunks P xs 2432 128 (Freiman.workReverse20260919_s0001_records_2432_2560 hnum)
    exact h2560
  have h2304 : ∀ x ∈ xs.drop 2304, P x := by
    apply all_of_chunks P xs 2304 128 (Freiman.workReverse20260919_s0001_records_2304_2432 hnum)
    exact h2432
  have h2176 : ∀ x ∈ xs.drop 2176, P x := by
    apply all_of_chunks P xs 2176 128 (Freiman.workReverse20260919_s0001_records_2176_2304 hnum)
    exact h2304
  have h2048 : ∀ x ∈ xs.drop 2048, P x := by
    apply all_of_chunks P xs 2048 128 (Freiman.workReverse20260919_s0001_records_2048_2176 hnum)
    exact h2176
  have h1920 : ∀ x ∈ xs.drop 1920, P x := by
    apply all_of_chunks P xs 1920 128 (Freiman.workReverse20260919_s0001_records_1920_2048 hnum)
    exact h2048
  have h1792 : ∀ x ∈ xs.drop 1792, P x := by
    apply all_of_chunks P xs 1792 128 (Freiman.workReverse20260919_s0001_records_1792_1920 hnum)
    exact h1920
  have h1664 : ∀ x ∈ xs.drop 1664, P x := by
    apply all_of_chunks P xs 1664 128 (Freiman.workReverse20260919_s0001_records_1664_1792 hnum)
    exact h1792
  have h1536 : ∀ x ∈ xs.drop 1536, P x := by
    apply all_of_chunks P xs 1536 128 (Freiman.workReverse20260919_s0001_records_1536_1664 hnum)
    exact h1664
  have h1408 : ∀ x ∈ xs.drop 1408, P x := by
    apply all_of_chunks P xs 1408 128 (Freiman.workReverse20260919_s0001_records_1408_1536 hnum)
    exact h1536
  have h1152 : ∀ x ∈ xs.drop 1152, P x := by
    apply all_of_chunks P xs 1152 256 (Freiman.workReverse20260919_s0001_records_1152_1408 hnum)
    exact h1408
  have h1024 : ∀ x ∈ xs.drop 1024, P x := by
    apply all_of_chunks P xs 1024 128 (Freiman.workReverse20260919_s0001_records_1024_1152 hnum)
    exact h1152
  have h896 : ∀ x ∈ xs.drop 896, P x := by
    apply all_of_chunks P xs 896 128 (Freiman.workReverse20260919_s0001_records_0896_1024 hnum)
    exact h1024
  have h768 : ∀ x ∈ xs.drop 768, P x := by
    apply all_of_chunks P xs 768 128 (Freiman.workReverse20260919_s0001_records_0768_0896 hnum)
    exact h896
  have h640 : ∀ x ∈ xs.drop 640, P x := by
    apply all_of_chunks P xs 640 128 (Freiman.workReverse20260919_s0001_records_0640_0768 hnum)
    exact h768
  have h512 : ∀ x ∈ xs.drop 512, P x := by
    apply all_of_chunks P xs 512 128 (Freiman.workReverse20260919_s0001_records_0512_0640 hnum)
    exact h640
  have h384 : ∀ x ∈ xs.drop 384, P x := by
    apply all_of_chunks P xs 384 128 (Freiman.workReverse20260919_s0001_records_0384_0512 hnum)
    exact h512
  have h256 : ∀ x ∈ xs.drop 256, P x := by
    apply all_of_chunks P xs 256 128 (Freiman.workReverse20260919_s0001_records_0256_0384 hnum)
    exact h384
  have h128 : ∀ x ∈ xs.drop 128, P x := by
    apply all_of_chunks P xs 128 128 (Freiman.workReverse20260919_s0001_records_0128_0256 hnum)
    exact h256
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 128 (Freiman.workReverse20260919_s0001_records_0000_0128 hnum)
    exact h128
  simpa only [List.drop_zero] using h0

end WorkReverseBundleStandalone_6ca5f492335faa34debb

#print axioms solution
