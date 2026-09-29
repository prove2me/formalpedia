-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_0704_0960
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:26:16.199564+00:00
-- url     : https://prove2.me/submissions/8d566065-65a7-4894-882c-cbcf52c360ad

import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0704_0736
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0736_0768
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0768_0800
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0800_0832
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0832_0864
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0864_0896
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0896_0928
import Theorems.Thm_Freiman_workReverse20260919_s0013_records_0928_0960

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
#print axioms all_of_chunks
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
#print axioms all_of_interval_split
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 704).take 256, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 704 832 960 (by decide) (by decide) (all_of_interval_split P xs 704 768 832 (by decide) (by decide) (all_of_interval_split P xs 704 736 768 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0704_0736 hnum) (Freiman.workReverse20260919_s0013_records_0736_0768 hnum)) (all_of_interval_split P xs 768 800 832 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0768_0800 hnum) (Freiman.workReverse20260919_s0013_records_0800_0832 hnum))) (all_of_interval_split P xs 832 896 960 (by decide) (by decide) (all_of_interval_split P xs 832 864 896 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0832_0864 hnum) (Freiman.workReverse20260919_s0013_records_0864_0896 hnum)) (all_of_interval_split P xs 896 928 960 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0896_0928 hnum) (Freiman.workReverse20260919_s0013_records_0928_0960 hnum))))
#print axioms solution
