-- Prove2me | solution 1 for DeletionCode.ConcreteInitialization.loadRoots_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:57:46.343969+00:00
-- url     : https://prove2.me/submissions/094e148e-c2e1-40a0-91fa-95e834e13bdc

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_ConcreteInitialization
import Theorems.Thm_DeletionCode_ConcreteFill_loadRoot_correct
import Theorems.Thm_DeletionCode_ConcreteModel_Model_sound_update
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_mono


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteInitialization
open Windows HeaderRecovery PartialWords SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteInitialization
theorem _root_.solution [DecidableEq B] (M : Model B x n k)
    (records : List (B × ℕ)) (mem : Bank B) (hs : M.Sound mem)
    (hvalid : ValidRoots M records) :
    ∃ result, loadRoots x n k M.header mem records = some result ∧ M.Sound result ∧
      (∀ b, Extends (mem b) (result b)) ∧
      (∀ b a, (b, a) ∈ records →
        WindowKnown (result b) 0 (negativeLength k (M.header b))) := by
  induction records generalizing mem with
  | nil =>
    refine ⟨mem, rfl, hs, ?_, ?_⟩
    · intro b j bit hj
      exact hj
    · intro b a hmem
      contradiction
  | cons record rest ih =>
    rcases record with ⟨b, a⟩
    have hocc := hvalid b a (by simp)
    obtain ⟨t, ht, hsound, hext, hread⟩ := ConcreteFill.loadRoot_correct
      x (negativePath k (M.header b) (M.long b)) n a
      (negativeLength k (M.header b)) (mem b) (negativeLength k (M.header b))
      (hs b) hocc.1 (by omega) hocc.2
    have hnext : M.Sound (Function.update mem b t) := M.sound_update mem hs b t hsound
    have htail : ValidRoots M rest := fun c j hj => hvalid c j (by simp [hj])
    obtain ⟨result, hresult, hrsound, hrext, hrknown⟩ := ih (Function.update mem b t) hnext htail
    have hstep : ∀ c, Extends (mem c) (Function.update mem b t c) := by
      intro c
      by_cases hcb : c = b
      · subst c
        simpa using hext
      · have hbc : b ≠ c := Ne.symm hcb
        intro j bit hj
        simpa [Function.update, hcb, hbc] using hj
    refine ⟨result, ?_, hrsound, ?_, ?_⟩
    · simpa only [loadRoots, ht, Option.bind_some] using hresult
    · intro c j bit hj
      exact hrext c j bit (hstep c j bit hj)
    · intro c j hj
      rcases List.mem_cons.mp hj with heq | hrest
      · cases heq
        apply windowKnown_mono (Function.update mem b t b) (result b) 0
          (negativeLength k (M.header b)) (hrext b)
        simpa using (show WindowKnown t 0 (negativeLength k (M.header b)) from ⟨_, hread⟩)
      · exact hrknown c j hrest
end DeletionCode.ConcreteInitialization
