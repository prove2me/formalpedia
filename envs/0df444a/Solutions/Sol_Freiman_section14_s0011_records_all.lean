-- Prove2me | solution 1 for Freiman.section14_s0011_records_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T17:07:12.039822+00:00
-- url     : https://prove2.me/submissions/8719117a-c3df-414e-ba66-cedfbd72be7d

import Theorems.Thm_Freiman_section14_s0011_records_0000_0032
import Theorems.Thm_Freiman_section14_s0011_records_0032_0096
import Theorems.Thm_Freiman_section14_s0011_records_0096_0160
import Theorems.Thm_Freiman_section14_s0011_records_0160_0224
import Theorems.Thm_Freiman_section14_s0011_records_0224_0288
import Theorems.Thm_Freiman_section14_s0011_records_0288_0352
import Theorems.Thm_Freiman_section14_s0011_records_0352_0416
import Theorems.Thm_Freiman_section14_s0011_records_0416_0480
import Theorems.Thm_Freiman_section14_s0011_records_0480_0544
import Theorems.Thm_Freiman_section14_s0011_records_0544_0608
import Theorems.Thm_Freiman_section14_s0011_records_0608_0672
import Theorems.Thm_Freiman_section14_s0011_records_0672_0736
import Theorems.Thm_Freiman_section14_s0011_records_0736_0800
import Theorems.Thm_Freiman_section14_s0011_records_0800_0864
import Theorems.Thm_Freiman_section14_s0011_records_0864_0928
import Theorems.Thm_Freiman_section14_s0011_records_0928_0992
import Theorems.Thm_Freiman_section14_s0011_records_0992_1056
import Theorems.Thm_Freiman_section14_s0011_records_1056_1120
import Theorems.Thm_Freiman_section14_s0011_records_1120_1184
import Theorems.Thm_Freiman_section14_s0011_records_1184_1248
import Theorems.Thm_Freiman_section14_s0011_records_1248_1312
import Theorems.Thm_Freiman_section14_s0011_records_1312_1376
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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (11 ∈ r.states))), section14RecordValid section14Catalog 11 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (11 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 11 r
  have h1376 : ∀ x ∈ xs.drop 1376, P x := by
    apply all_empty P _
    rfl
  have h1312 : ∀ x ∈ xs.drop 1312, P x := by
    apply all_of_chunks P xs 1312 64 (Freiman.section14_s0011_records_1312_1376 hnum)
    exact h1376
  have h1248 : ∀ x ∈ xs.drop 1248, P x := by
    apply all_of_chunks P xs 1248 64 (Freiman.section14_s0011_records_1248_1312 hnum)
    exact h1312
  have h1184 : ∀ x ∈ xs.drop 1184, P x := by
    apply all_of_chunks P xs 1184 64 (Freiman.section14_s0011_records_1184_1248 hnum)
    exact h1248
  have h1120 : ∀ x ∈ xs.drop 1120, P x := by
    apply all_of_chunks P xs 1120 64 (Freiman.section14_s0011_records_1120_1184 hnum)
    exact h1184
  have h1056 : ∀ x ∈ xs.drop 1056, P x := by
    apply all_of_chunks P xs 1056 64 (Freiman.section14_s0011_records_1056_1120 hnum)
    exact h1120
  have h992 : ∀ x ∈ xs.drop 992, P x := by
    apply all_of_chunks P xs 992 64 (Freiman.section14_s0011_records_0992_1056 hnum)
    exact h1056
  have h928 : ∀ x ∈ xs.drop 928, P x := by
    apply all_of_chunks P xs 928 64 (Freiman.section14_s0011_records_0928_0992 hnum)
    exact h992
  have h864 : ∀ x ∈ xs.drop 864, P x := by
    apply all_of_chunks P xs 864 64 (Freiman.section14_s0011_records_0864_0928 hnum)
    exact h928
  have h800 : ∀ x ∈ xs.drop 800, P x := by
    apply all_of_chunks P xs 800 64 (Freiman.section14_s0011_records_0800_0864 hnum)
    exact h864
  have h736 : ∀ x ∈ xs.drop 736, P x := by
    apply all_of_chunks P xs 736 64 (Freiman.section14_s0011_records_0736_0800 hnum)
    exact h800
  have h672 : ∀ x ∈ xs.drop 672, P x := by
    apply all_of_chunks P xs 672 64 (Freiman.section14_s0011_records_0672_0736 hnum)
    exact h736
  have h608 : ∀ x ∈ xs.drop 608, P x := by
    apply all_of_chunks P xs 608 64 (Freiman.section14_s0011_records_0608_0672 hnum)
    exact h672
  have h544 : ∀ x ∈ xs.drop 544, P x := by
    apply all_of_chunks P xs 544 64 (Freiman.section14_s0011_records_0544_0608 hnum)
    exact h608
  have h480 : ∀ x ∈ xs.drop 480, P x := by
    apply all_of_chunks P xs 480 64 (Freiman.section14_s0011_records_0480_0544 hnum)
    exact h544
  have h416 : ∀ x ∈ xs.drop 416, P x := by
    apply all_of_chunks P xs 416 64 (Freiman.section14_s0011_records_0416_0480 hnum)
    exact h480
  have h352 : ∀ x ∈ xs.drop 352, P x := by
    apply all_of_chunks P xs 352 64 (Freiman.section14_s0011_records_0352_0416 hnum)
    exact h416
  have h288 : ∀ x ∈ xs.drop 288, P x := by
    apply all_of_chunks P xs 288 64 (Freiman.section14_s0011_records_0288_0352 hnum)
    exact h352
  have h224 : ∀ x ∈ xs.drop 224, P x := by
    apply all_of_chunks P xs 224 64 (Freiman.section14_s0011_records_0224_0288 hnum)
    exact h288
  have h160 : ∀ x ∈ xs.drop 160, P x := by
    apply all_of_chunks P xs 160 64 (Freiman.section14_s0011_records_0160_0224 hnum)
    exact h224
  have h96 : ∀ x ∈ xs.drop 96, P x := by
    apply all_of_chunks P xs 96 64 (Freiman.section14_s0011_records_0096_0160 hnum)
    exact h160
  have h32 : ∀ x ∈ xs.drop 32, P x := by
    apply all_of_chunks P xs 32 64 (Freiman.section14_s0011_records_0032_0096 hnum)
    exact h96
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 32 (Freiman.section14_s0011_records_0000_0032 hnum)
    exact h32
  simpa only [List.drop_zero] using h0

#print axioms solution
