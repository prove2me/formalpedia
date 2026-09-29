-- Prove2me | solution 1 for Freiman.lowerHistory_witness_metadata_05
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T09:04:04.683746+00:00
-- url     : https://prove2.me/submissions/b71db851-c490-4603-8ade-28a05c1fbf4b

import Theorems.Thm_Freiman_lowerHistory_witness_metadata_05_part_01
import Theorems.Thm_Freiman_lowerHistory_witness_metadata_05_part_02
import Theorems.Thm_Freiman_lowerHistory_witness_metadata_05_part_03
import Theorems.Thm_Freiman_lowerHistory_witness_metadata_05_part_04
import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic.NormNum
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem map_in_chunks {α β : Type} (xs : List α) (f : α → β)
    (size n : ℕ) :
    (xs.take (n*size)).map f =
      (List.range n).flatMap (fun j => ((xs.drop (j*size)).take size).map f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.take_add, List.map_append, ih,
      List.range_succ, List.flatMap_append]
    simp
private theorem maps_eq_of_chunks {α β γ : Type} (xs : List α) (ys : List β)
    (f : α → γ) (g : β → γ) (size count : ℕ)
    (hx : xs.length ≤ count*size) (hy : ys.length ≤ count*size)
    (hc : ∀ j ∈ List.range count,
      ((xs.drop (j*size)).take size).map f = ((ys.drop (j*size)).take size).map g) :
    xs.map f = ys.map g := by
  have h1 := map_in_chunks xs f size count
  have h2 := map_in_chunks ys g size count
  rw [List.take_of_length_le hx] at h1
  rw [List.take_of_length_le hy] at h2
  rw [h1,h2,List.flatMap_def,List.flatMap_def]
  exact congrArg List.flatten (List.map_congr_left hc)
theorem solution : lowerHistoryWitnesses05.toList.map
    (fun w => (w.lowerBound, w.upperBound, w.rectangle)) =
  (lowerHistoryWitnessIds05.toList.zip ([2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,6] : List ℕ)).map
    (fun z => (lowerHistoryBound z.1.1, lowerHistoryBound z.1.2,
      lowerHistoryRectangles[z.2]?.getD ⟨0,1,0,1⟩)) := by
  apply maps_eq_of_chunks lowerHistoryWitnesses05.toList (lowerHistoryWitnessIds05.toList.zip ([2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,6] : List ℕ)) (fun w : CertWitness => (w.lowerBound,w.upperBound,w.rectangle)) (fun z : (ℕ × ℕ) × ℕ => (lowerHistoryBound z.1.1,lowerHistoryBound z.1.2,lowerHistoryRectangles[z.2]?.getD ⟨0,1,0,1⟩)) 50 4 (by decide) (by decide)
  intro j hj
  simp only [List.range_succ,List.range_zero,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,false_or,or_assoc] at hj
  rcases hj with rfl | rfl | rfl | rfl
  · exact Freiman.lowerHistory_witness_metadata_05_part_01
  · exact Freiman.lowerHistory_witness_metadata_05_part_02
  · exact Freiman.lowerHistory_witness_metadata_05_part_03
  · exact Freiman.lowerHistory_witness_metadata_05_part_04
#print axioms solution
