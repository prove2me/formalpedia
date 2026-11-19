-- Prove2me | solution 1 for DeletionCode.ConcreteInitialization.initialization_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:58:28.019371+00:00
-- url     : https://prove2.me/submissions/86941d81-4e58-4d90-b5ce-acc259ab1475

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_ConcreteInitialization
import Theorems.Thm_DeletionCode_ConcreteInitialization_loadRoots_correct
import Theorems.Thm_DeletionCode_ConcreteInitialization_root_records_exist
import Theorems.Thm_DeletionCode_ConcreteModel_Model_window_bound
import Theorems.Thm_DeletionCode_PartialWords_empty_sound
import Theorems.Thm_DeletionCode_Recovery_initial_wellFormed
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_subblock


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteInitialization
open Windows HeaderRecovery PartialWords SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteInitialization
theorem _root_.solution [Fintype B] [DecidableEq B] (M : Model B x n k) :
    ∃ records mem, records.length = rootCount M ∧
      loadRoots x n k M.header (fun _ => empty) records = some mem ∧
      M.Invariant (Recovery.initial M.schedule) mem := by
  classical
  obtain ⟨records, hlength, hvalid, hroots⟩ := root_records_exist M
  have hempty : M.Sound (fun _ => empty) := fun b =>
    empty_sound (negativePath k (M.header b) (M.long b)) (negativeLength k (M.header b))
  obtain ⟨mem, hload, hsound, _, hknown⟩ := loadRoots_correct M records (fun _ => empty) hempty hvalid
  have hrootKnown : ∀ b, M.schedule.root b →
      WindowKnown (mem b) 0 (negativeLength k (M.header b)) := by
    intro b hb
    obtain ⟨a, ha⟩ := hroots b hb
    exact hknown b a ha
  refine ⟨records, mem, hlength, hload, Recovery.initial_wellFormed M.schedule, hsound, ?_⟩
  constructor
  · intro b w hseed
    by_cases hb : M.schedule.root b
    · have hw : w = 0 := by simpa [Recovery.initial, hb] using hseed.symm
      subst w
      have hL : windowLength k ≤ negativeLength k (M.header b) := by
        simpa [windowStart] using M.window_bound b 0
      have hk : k ≤ negativeLength k (M.header b) := by
        unfold windowLength at hL
        omega
      obtain ⟨bits, hread⟩ := windowKnown_subblock (mem b) 0
        (negativeLength k (M.header b)) 0 k (hrootKnown b hb) (by omega) (by omega)
      refine ⟨0, bits, by omega, ?_⟩
      simpa [windowStart] using hread
    · simp [Recovery.initial, hb] at hseed
  · intro b w hdone
    have hb : M.schedule.root b := by simpa [Recovery.State.Done, Recovery.initial] using hdone
    exact windowKnown_subblock (mem b) 0 (negativeLength k (M.header b))
      (windowStart (negativeExtra k (M.header b)) w) (windowLength k)
      (hrootKnown b hb) (by omega) (by simpa using M.window_bound b w)
end DeletionCode.ConcreteInitialization
