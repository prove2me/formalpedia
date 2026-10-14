-- Prove2me | solution 1 for BookProof.ChapterDutchBook.Coherent.empty
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:03:30.260207+00:00
-- url     : https://prove2.me/submissions/8731109f-e547-48ab-bdc2-3f7e98713a7d

-- Generated from ChapterDutchBook.lean — theorem BookProof.ChapterDutchBook.Coherent.empty
import Mathlib
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook


open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

theorem solution{Pr : Finset Ω → ℝ} (h : Coherent Pr) : Pr (∅ : Finset Ω) = 0 := by
  by_contra hne
  apply h
  refine ⟨1, fun _ => ∅, fun _ => Pr ∅, fun ω => ?_⟩
  simp [payoff, betIndicator]
  nlinarith [mul_self_pos.mpr hne]
