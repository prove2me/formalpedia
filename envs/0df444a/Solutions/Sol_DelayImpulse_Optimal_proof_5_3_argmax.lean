-- Prove2me | solution 1 for DelayImpulse.Optimal.proof_5_3_argmax
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:30:57.013569+00:00
-- url     : https://prove2.me/submissions/1c8b4365-9edc-49fd-acf5-915dc11e221d

import Mathlib

open MeasureTheory

theorem solution {Ω E : Type} [MeasurableSpace E] [MeasurableSingletonClass E]
    (G : MeasurableSpace Ω) (U : Finset E) (hU : U.Nonempty) (X : E → Ω → ℝ)
    (hX : ∀ β ∈ U, Measurable[G] (X β)) :
    ∃ b : Ω → E, Measurable[G] b ∧ (∀ ω, b ω ∈ U) ∧
      ∀ ω, X (b ω) ω = U.sup' hU (fun β => X β ω) := by
  classical
  revert hX
  induction hU using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro hX
    refine ⟨fun _ => a, measurable_const, fun ω => Finset.mem_singleton_self a, ?_⟩
    intro ω; simp
  | cons a s ha hs ih =>
    intro hX
    have hXs : ∀ β ∈ s, Measurable[G] (X β) := fun β hβ => hX β (Finset.mem_cons_of_mem hβ)
    obtain ⟨b, hbm, hbU, hbX⟩ := ih hXs
    have hXa : Measurable[G] (X a) := hX a (Finset.mem_cons_self a s)
    have hsupm : Measurable[G] (fun ω => s.sup' hs (fun β => X β ω)) := by
      have h := Finset.measurable_sup' hs hXs
      convert h using 1
      funext ω; simp [Finset.sup'_apply]
    let S : Set Ω := {ω | s.sup' hs (fun β => X β ω) ≤ X a ω}
    have hS : MeasurableSet[G] S := measurableSet_le hsupm hXa
    refine ⟨fun ω => if s.sup' hs (fun β => X β ω) ≤ X a ω then a else b ω, ?_, ?_, ?_⟩
    · exact Measurable.ite hS measurable_const hbm
    · intro ω
      dsimp only
      split_ifs
      · exact Finset.mem_cons_self a s
      · exact Finset.mem_cons_of_mem (hbU ω)
    · intro ω
      dsimp only
      rw [Finset.sup'_cons]
      split_ifs with h
      · exact (max_eq_left h).symm
      · rw [hbX ω]; exact (max_eq_right (le_of_lt (not_le.1 h))).symm
