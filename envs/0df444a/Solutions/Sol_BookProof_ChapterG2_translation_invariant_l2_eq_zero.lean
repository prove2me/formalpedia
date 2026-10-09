-- Prove2me | solution 1 for BookProof.ChapterG2.translation_invariant_l2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:21:15.460935+00:00
-- url     : https://prove2.me/submissions/56fc34fe-88d7-4075-a6fb-d47972c464f1

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.translation_invariant_l2_eq_zero
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution {G : Type*} [Group G] [Infinite G]
    (Ψ : lp (fun _ : G => ℂ) 2) (hΨ : ∀ g x : G, Ψ (g * x) = Ψ x) : Ψ = 0 := by

  ext x;
  have h_const : ∀ g : G, Ψ g = Ψ 1 := by
    exact fun g => by simpa using hΨ g 1;
  have := Ψ.2.summable;
  simp_all [ summable_const_iff ]
