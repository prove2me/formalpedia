-- Prove2me | solution 1 for BB5.no_halt_RA
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-22T20:34:39.643522+00:00
-- url     : https://prove2.me/submissions/ba0f06c6-f7e0-4f36-933f-b51f94c4c1a9

import Mathlib
import Definitions.Def_FCP_BusyBeaver

theorem solution (M : FCP.BusyBeaver.TM 5)
    (hA0 : (M.trans ⟨0, by omega⟩ false).2.1 = true ∧
           (M.trans ⟨0, by omega⟩ false).2.2 = some ⟨0, by omega⟩) :
    ∀ t : ℕ, FCP.BusyBeaver.run M (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  obtain ⟨hd, hs⟩ := hA0
  -- Invariant: after t steps the machine is in state A, at position t, with blank tape from t on.
  have key : ∀ t : ℕ, ∃ c : FCP.BusyBeaver.Config 5,
      FCP.BusyBeaver.run M (FCP.BusyBeaver.init (by omega)) t = some c ∧
      c.state = ⟨0, by omega⟩ ∧ c.head = (t : ℤ) ∧ ∀ i : ℤ, (t : ℤ) ≤ i → c.tape i = false := by
    intro t
    induction t with
    | zero => exact ⟨_, rfl, rfl, rfl, fun _ _ => rfl⟩
    | succ t ih =>
      obtain ⟨c, hc, hst, hh, ht⟩ := ih
      have hread : c.tape c.head = false := ht _ (by omega)
      rcases hM : M.trans ⟨0, (by decide : 0 < 5)⟩ false with ⟨w, d, s⟩
      rw [hM] at hd hs
      simp only at hd hs
      subst hd hs
      refine ⟨⟨⟨0, (by decide : 0 < 5)⟩, c.head + 1, Function.update c.tape c.head w⟩, ?_, rfl, ?_, ?_⟩
      · show (FCP.BusyBeaver.run M _ t).bind (FCP.BusyBeaver.step M) = _
        rw [hc]
        show FCP.BusyBeaver.step M c = _
        unfold FCP.BusyBeaver.step
        rw [hread, hst, hM]
        rfl
      · show c.head + 1 = ((t + 1 : ℕ) : ℤ)
        omega
      · intro i hi
        show Function.update c.tape c.head w i = false
        rw [Function.update_apply, if_neg (by omega)]
        exact ht i (by omega)
  intro t h
  obtain ⟨c, hc, -⟩ := key t
  rw [hc] at h
  exact Option.some_ne_none c h
