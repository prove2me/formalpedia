-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_coverage_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T05:48:31.187674+00:00
-- url     : https://prove2.me/submissions/cf93b17f-2d60-41d2-9f56-11bb919b6168

import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0000_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0001_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0002_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0003_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0004_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0005_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0006_all
import Theorems.Thm_Freiman_workReverse20260919_s0005_coverage0007_all
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

namespace WorkReverseBundleStandalone_60145b206f62dd10e594
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
theorem _root_.solution : section14Coverage section14Catalog 5 := by
  let xs := (section14State section14Catalog 5).plans
  let P := fun pl : Section14Plan => ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 5), section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j
  have h8 : ∀ x ∈ xs.drop 8, P x := by
    apply all_empty P _
    rfl
  have h7 : ∀ x ∈ xs.drop 7, P x := by
    apply all_of_chunks P xs 7 1 (Freiman.workReverse20260919_s0005_coverage0007_all)
    exact h8
  have h6 : ∀ x ∈ xs.drop 6, P x := by
    apply all_of_chunks P xs 6 1 (Freiman.workReverse20260919_s0005_coverage0006_all)
    exact h7
  have h5 : ∀ x ∈ xs.drop 5, P x := by
    apply all_of_chunks P xs 5 1 (Freiman.workReverse20260919_s0005_coverage0005_all)
    exact h6
  have h4 : ∀ x ∈ xs.drop 4, P x := by
    apply all_of_chunks P xs 4 1 (Freiman.workReverse20260919_s0005_coverage0004_all)
    exact h5
  have h3 : ∀ x ∈ xs.drop 3, P x := by
    apply all_of_chunks P xs 3 1 (Freiman.workReverse20260919_s0005_coverage0003_all)
    exact h4
  have h2 : ∀ x ∈ xs.drop 2, P x := by
    apply all_of_chunks P xs 2 1 (Freiman.workReverse20260919_s0005_coverage0002_all)
    exact h3
  have h1 : ∀ x ∈ xs.drop 1, P x := by
    apply all_of_chunks P xs 1 1 (Freiman.workReverse20260919_s0005_coverage0001_all)
    exact h2
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 1 (Freiman.workReverse20260919_s0005_coverage0000_all)
    exact h1
  simpa only [section14Coverage, xs, P, List.drop_zero] using h0

end WorkReverseBundleStandalone_60145b206f62dd10e594

#print axioms solution
