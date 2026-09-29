-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:40:07.279464+00:00
-- url     : https://prove2.me/submissions/135b9af4-8518-4993-94b8-8595fe948234

import Theorems.Thm_Freiman_workReverse20260919_s0005_records_0000_0128
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_0128_0256
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_0256_0512
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_0512_0640
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_0640_0768
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_0768_0896
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_0896_1024
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_1024_1152
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_1152_1280
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_1280_1408
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_1408_1536
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_1536_1664
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_1664_1792
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_1792_1920
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_1920_2048
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2048_2176
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2176_2304
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2304_2368
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2368_2496
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2496_2624
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2624_2688
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2688_2752
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2752_2816
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2816_2880
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2880_2944
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_2944_3008
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3008_3072
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3072_3136
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3136_3200
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3200_3328
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3328_3456
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3456_3584
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3584_3712
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3712_3776
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3776_3840
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3840_3904
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3904_3968
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_3968_4096
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_4096_4224
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_4224_4352
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_4352_4416
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_4416_4480
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_4480_4544
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_4544_4608
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_4608_4672
import Theorems.Thm_Freiman_workReverse20260919_s0005_records_4672_4748
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

namespace WorkReverseBundleStandalone_65ca79c53b64df6426de
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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (5 ∈ r.states))), section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  have h4748 : ∀ x ∈ xs.drop 4748, P x := by
    apply all_empty P _
    rfl
  have h4672 : ∀ x ∈ xs.drop 4672, P x := by
    apply all_of_chunks P xs 4672 76 (Freiman.workReverse20260919_s0005_records_4672_4748 hnum)
    exact h4748
  have h4608 : ∀ x ∈ xs.drop 4608, P x := by
    apply all_of_chunks P xs 4608 64 (Freiman.workReverse20260919_s0005_records_4608_4672 hnum)
    exact h4672
  have h4544 : ∀ x ∈ xs.drop 4544, P x := by
    apply all_of_chunks P xs 4544 64 (Freiman.workReverse20260919_s0005_records_4544_4608 hnum)
    exact h4608
  have h4480 : ∀ x ∈ xs.drop 4480, P x := by
    apply all_of_chunks P xs 4480 64 (Freiman.workReverse20260919_s0005_records_4480_4544 hnum)
    exact h4544
  have h4416 : ∀ x ∈ xs.drop 4416, P x := by
    apply all_of_chunks P xs 4416 64 (Freiman.workReverse20260919_s0005_records_4416_4480 hnum)
    exact h4480
  have h4352 : ∀ x ∈ xs.drop 4352, P x := by
    apply all_of_chunks P xs 4352 64 (Freiman.workReverse20260919_s0005_records_4352_4416 hnum)
    exact h4416
  have h4224 : ∀ x ∈ xs.drop 4224, P x := by
    apply all_of_chunks P xs 4224 128 (Freiman.workReverse20260919_s0005_records_4224_4352 hnum)
    exact h4352
  have h4096 : ∀ x ∈ xs.drop 4096, P x := by
    apply all_of_chunks P xs 4096 128 (Freiman.workReverse20260919_s0005_records_4096_4224 hnum)
    exact h4224
  have h3968 : ∀ x ∈ xs.drop 3968, P x := by
    apply all_of_chunks P xs 3968 128 (Freiman.workReverse20260919_s0005_records_3968_4096 hnum)
    exact h4096
  have h3904 : ∀ x ∈ xs.drop 3904, P x := by
    apply all_of_chunks P xs 3904 64 (Freiman.workReverse20260919_s0005_records_3904_3968 hnum)
    exact h3968
  have h3840 : ∀ x ∈ xs.drop 3840, P x := by
    apply all_of_chunks P xs 3840 64 (Freiman.workReverse20260919_s0005_records_3840_3904 hnum)
    exact h3904
  have h3776 : ∀ x ∈ xs.drop 3776, P x := by
    apply all_of_chunks P xs 3776 64 (Freiman.workReverse20260919_s0005_records_3776_3840 hnum)
    exact h3840
  have h3712 : ∀ x ∈ xs.drop 3712, P x := by
    apply all_of_chunks P xs 3712 64 (Freiman.workReverse20260919_s0005_records_3712_3776 hnum)
    exact h3776
  have h3584 : ∀ x ∈ xs.drop 3584, P x := by
    apply all_of_chunks P xs 3584 128 (Freiman.workReverse20260919_s0005_records_3584_3712 hnum)
    exact h3712
  have h3456 : ∀ x ∈ xs.drop 3456, P x := by
    apply all_of_chunks P xs 3456 128 (Freiman.workReverse20260919_s0005_records_3456_3584 hnum)
    exact h3584
  have h3328 : ∀ x ∈ xs.drop 3328, P x := by
    apply all_of_chunks P xs 3328 128 (Freiman.workReverse20260919_s0005_records_3328_3456 hnum)
    exact h3456
  have h3200 : ∀ x ∈ xs.drop 3200, P x := by
    apply all_of_chunks P xs 3200 128 (Freiman.workReverse20260919_s0005_records_3200_3328 hnum)
    exact h3328
  have h3136 : ∀ x ∈ xs.drop 3136, P x := by
    apply all_of_chunks P xs 3136 64 (Freiman.workReverse20260919_s0005_records_3136_3200 hnum)
    exact h3200
  have h3072 : ∀ x ∈ xs.drop 3072, P x := by
    apply all_of_chunks P xs 3072 64 (Freiman.workReverse20260919_s0005_records_3072_3136 hnum)
    exact h3136
  have h3008 : ∀ x ∈ xs.drop 3008, P x := by
    apply all_of_chunks P xs 3008 64 (Freiman.workReverse20260919_s0005_records_3008_3072 hnum)
    exact h3072
  have h2944 : ∀ x ∈ xs.drop 2944, P x := by
    apply all_of_chunks P xs 2944 64 (Freiman.workReverse20260919_s0005_records_2944_3008 hnum)
    exact h3008
  have h2880 : ∀ x ∈ xs.drop 2880, P x := by
    apply all_of_chunks P xs 2880 64 (Freiman.workReverse20260919_s0005_records_2880_2944 hnum)
    exact h2944
  have h2816 : ∀ x ∈ xs.drop 2816, P x := by
    apply all_of_chunks P xs 2816 64 (Freiman.workReverse20260919_s0005_records_2816_2880 hnum)
    exact h2880
  have h2752 : ∀ x ∈ xs.drop 2752, P x := by
    apply all_of_chunks P xs 2752 64 (Freiman.workReverse20260919_s0005_records_2752_2816 hnum)
    exact h2816
  have h2688 : ∀ x ∈ xs.drop 2688, P x := by
    apply all_of_chunks P xs 2688 64 (Freiman.workReverse20260919_s0005_records_2688_2752 hnum)
    exact h2752
  have h2624 : ∀ x ∈ xs.drop 2624, P x := by
    apply all_of_chunks P xs 2624 64 (Freiman.workReverse20260919_s0005_records_2624_2688 hnum)
    exact h2688
  have h2496 : ∀ x ∈ xs.drop 2496, P x := by
    apply all_of_chunks P xs 2496 128 (Freiman.workReverse20260919_s0005_records_2496_2624 hnum)
    exact h2624
  have h2368 : ∀ x ∈ xs.drop 2368, P x := by
    apply all_of_chunks P xs 2368 128 (Freiman.workReverse20260919_s0005_records_2368_2496 hnum)
    exact h2496
  have h2304 : ∀ x ∈ xs.drop 2304, P x := by
    apply all_of_chunks P xs 2304 64 (Freiman.workReverse20260919_s0005_records_2304_2368 hnum)
    exact h2368
  have h2176 : ∀ x ∈ xs.drop 2176, P x := by
    apply all_of_chunks P xs 2176 128 (Freiman.workReverse20260919_s0005_records_2176_2304 hnum)
    exact h2304
  have h2048 : ∀ x ∈ xs.drop 2048, P x := by
    apply all_of_chunks P xs 2048 128 (Freiman.workReverse20260919_s0005_records_2048_2176 hnum)
    exact h2176
  have h1920 : ∀ x ∈ xs.drop 1920, P x := by
    apply all_of_chunks P xs 1920 128 (Freiman.workReverse20260919_s0005_records_1920_2048 hnum)
    exact h2048
  have h1792 : ∀ x ∈ xs.drop 1792, P x := by
    apply all_of_chunks P xs 1792 128 (Freiman.workReverse20260919_s0005_records_1792_1920 hnum)
    exact h1920
  have h1664 : ∀ x ∈ xs.drop 1664, P x := by
    apply all_of_chunks P xs 1664 128 (Freiman.workReverse20260919_s0005_records_1664_1792 hnum)
    exact h1792
  have h1536 : ∀ x ∈ xs.drop 1536, P x := by
    apply all_of_chunks P xs 1536 128 (Freiman.workReverse20260919_s0005_records_1536_1664 hnum)
    exact h1664
  have h1408 : ∀ x ∈ xs.drop 1408, P x := by
    apply all_of_chunks P xs 1408 128 (Freiman.workReverse20260919_s0005_records_1408_1536 hnum)
    exact h1536
  have h1280 : ∀ x ∈ xs.drop 1280, P x := by
    apply all_of_chunks P xs 1280 128 (Freiman.workReverse20260919_s0005_records_1280_1408 hnum)
    exact h1408
  have h1152 : ∀ x ∈ xs.drop 1152, P x := by
    apply all_of_chunks P xs 1152 128 (Freiman.workReverse20260919_s0005_records_1152_1280 hnum)
    exact h1280
  have h1024 : ∀ x ∈ xs.drop 1024, P x := by
    apply all_of_chunks P xs 1024 128 (Freiman.workReverse20260919_s0005_records_1024_1152 hnum)
    exact h1152
  have h896 : ∀ x ∈ xs.drop 896, P x := by
    apply all_of_chunks P xs 896 128 (Freiman.workReverse20260919_s0005_records_0896_1024 hnum)
    exact h1024
  have h768 : ∀ x ∈ xs.drop 768, P x := by
    apply all_of_chunks P xs 768 128 (Freiman.workReverse20260919_s0005_records_0768_0896 hnum)
    exact h896
  have h640 : ∀ x ∈ xs.drop 640, P x := by
    apply all_of_chunks P xs 640 128 (Freiman.workReverse20260919_s0005_records_0640_0768 hnum)
    exact h768
  have h512 : ∀ x ∈ xs.drop 512, P x := by
    apply all_of_chunks P xs 512 128 (Freiman.workReverse20260919_s0005_records_0512_0640 hnum)
    exact h640
  have h256 : ∀ x ∈ xs.drop 256, P x := by
    apply all_of_chunks P xs 256 256 (Freiman.workReverse20260919_s0005_records_0256_0512 hnum)
    exact h512
  have h128 : ∀ x ∈ xs.drop 128, P x := by
    apply all_of_chunks P xs 128 128 (Freiman.workReverse20260919_s0005_records_0128_0256 hnum)
    exact h256
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 128 (Freiman.workReverse20260919_s0005_records_0000_0128 hnum)
    exact h128
  simpa only [List.drop_zero] using h0

end WorkReverseBundleStandalone_65ca79c53b64df6426de

#print axioms solution
