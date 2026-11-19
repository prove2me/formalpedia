-- Prove2me | solution 1 for DeletionCode.ConcreteInitialization.root_records_exist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:57:53.256485+00:00
-- url     : https://prove2.me/submissions/518e5a67-e646-48ff-a260-ce90f056c535

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_ConcreteInitialization

set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteInitialization
open Windows HeaderRecovery PartialWords SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteInitialization
theorem _root_.solution [Fintype B] (M : Model B x n k) :
    ∃ records : List (B × ℕ), records.length = rootCount M ∧ ValidRoots M records ∧
      (∀ b, M.schedule.root b → ∃ a, (b, a) ∈ records) := by
  classical
  let roots := Finset.univ.filter M.schedule.root
  let pos : B → ℕ := fun b => if hr : M.schedule.root b then
    Classical.choose (M.root_occurrence b hr) else 0
  let records := roots.toList.map (fun b => (b, pos b))
  have hpos : ∀ b, M.schedule.root b →
      pos b + negativeLength k (M.header b) ≤ n ∧
      Agree x (pos b) (negativePath k (M.header b) (M.long b)) 0
        (negativeLength k (M.header b)) := by
    intro b hb
    dsimp [pos]
    rw [dif_pos hb]
    exact Classical.choose_spec (M.root_occurrence b hb)
  refine ⟨records, ?_, ?_, ?_⟩
  · simp [records, roots, rootCount]
  · intro b a hmem
    obtain ⟨c, hc, heq⟩ := List.mem_map.mp hmem
    have hroot : M.schedule.root c := by simpa [roots] using hc
    have hcpos := hpos c hroot
    cases heq
    exact hcpos
  · intro b hb
    refine ⟨pos b, List.mem_map.mpr ⟨b, ?_, rfl⟩⟩
    simpa [roots] using hb
end DeletionCode.ConcreteInitialization
