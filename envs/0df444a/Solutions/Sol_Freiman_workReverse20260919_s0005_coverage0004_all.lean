-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_coverage0004_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T23:21:37.35365+00:00
-- url     : https://prove2.me/submissions/318c1431-ad01-462a-bbfc-ec48cd789bce

import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0004_parents_0000_0064
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0004_parents_0064_0128
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0004_parents_0128_0192
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0004_parents_0192_0256
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

namespace WorkReverseBundleStandalone_87d036b045503a87c680
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
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 4).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 5), section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  intro pl hpl
  let xs := section14Parents section14Catalog (section14State section14Catalog 5)
  let P := fun b : Section14Parent => section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j
  have h256 : ∀ x ∈ xs.drop 256, P x := by
    apply all_empty P _
    rfl
  have h192 : ∀ x ∈ xs.drop 192, P x := by
    apply all_of_chunks P xs 192 64 (Freiman.workReverse20260919_s0005_coverage0004_parents_0192_0256 pl hpl)
    exact h256
  have h128 : ∀ x ∈ xs.drop 128, P x := by
    apply all_of_chunks P xs 128 64 (Freiman.workReverse20260919_s0005_coverage0004_parents_0128_0192 pl hpl)
    exact h192
  have h64 : ∀ x ∈ xs.drop 64, P x := by
    apply all_of_chunks P xs 64 64 (Freiman.workReverse20260919_s0005_coverage0004_parents_0064_0128 pl hpl)
    exact h128
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 64 (Freiman.workReverse20260919_s0005_coverage0004_parents_0000_0064 pl hpl)
    exact h64
  simpa only [List.drop_zero] using h0

end WorkReverseBundleStandalone_87d036b045503a87c680

#print axioms solution
