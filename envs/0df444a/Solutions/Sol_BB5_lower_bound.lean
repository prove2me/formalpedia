-- Prove2me | solution 1 for BB5.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-22T15:09:09.33963+00:00
-- url     : https://prove2.me/submissions/488b80d2-d0e3-4951-878c-2eacdbc7284e

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner
import Theorems.Thm_BB5_champion_halts

open FCP.BusyBeaver

/-- A machine started from a fixed configuration has at most one halting time. -/
private lemma haltsIn_unique {n : ℕ} {M : TM n} {c : Config n} {t₁ t₂ : ℕ}
    (h₁ : HaltsIn M c t₁) (h₂ : HaltsIn M c t₂) : t₁ = t₂ := by
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · exact (h₂.2 t₁ hlt h₁.1).elim
  · exact heq
  · exact (h₁.2 t₂ hgt h₂.1).elim

/-- The starting configuration does not depend on the proof that `0 < n`. -/
private lemma init_proof_irrel {n : ℕ} (h₁ h₂ : 0 < n) : init h₁ = init h₂ := by
  simp [init]

/-- The halting time of a machine, or 0 if it never halts. -/
private noncomputable def haltTime (M : TM 5) : ℕ := by
  classical
  exact if h : ∃ (hp : 0 < 5) (t : ℕ), HaltsIn M (init hp) t then
    Classical.choose (Classical.choose_spec h)
  else 0

theorem solution : 47176870 ≤ FCP.BusyBeaver.BB 5 := by
  let S : Set ℕ := {t : ℕ | ∃ (M : TM 5) (hp : 0 < 5), HaltsIn M (init hp) t}
  letI : Finite (TM 5) :=
    Finite.of_injective (fun M : TM 5 => M.trans) (by
      intro a b h
      cases a
      cases b
      simp_all)
  have hsub : S ⊆ Set.range haltTime := by
    intro t ht
    rcases ht with ⟨M, hp, hhal⟩
    refine ⟨M, ?_⟩
    have hM : ∃ (hp : 0 < 5) (t : ℕ), HaltsIn M (init hp) t := ⟨hp, t, hhal⟩
    rw [haltTime, dif_pos hM]
    have hfhal : HaltsIn M (init (Classical.choose hM))
        (Classical.choose (Classical.choose_spec hM)) :=
      Classical.choose_spec (Classical.choose_spec hM)
    apply haltsIn_unique hfhal
    simpa [init_proof_irrel] using hhal
  have hfin : S.Finite := (Set.finite_range haltTime).subset hsub
  have hbdd : BddAbove S := hfin.bddAbove
  have hmem : 47176870 ∈ S := by
    exact ⟨BB5.winner, by omega, BB5.champion_halts⟩
  simpa [S, FCP.BusyBeaver.BB] using (le_csSup hbdd hmem)
