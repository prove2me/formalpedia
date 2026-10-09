-- Prove2me | solution 1 for BookProof.ChapterDutchBook.Coherent.additive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:14.867995+00:00
-- url     : https://prove2.me/submissions/e7066f29-81e2-4ec0-9503-d3d2ffe8edd0

-- Generated from ChapterDutchBook.lean — solution of BookProof.ChapterDutchBook.Coherent.additive
import Mathlib
import Definitions.Def_ChapterDutchBook
import Theorems.Thm_BookProof_ChapterDutchBook_payoff_triple
open BookProof.ChapterDutchBook



open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

variable {Ω : Type*} [DecidableEq Ω]

set_option maxHeartbeats 1000000 in
theorem solution {Pr : Finset Ω → ℝ} (h : Coherent Pr)
    {A B : Finset Ω} (hAB : Disjoint A B) :
    Pr (A ∪ B) = Pr A + Pr B := by

  by_contra hne
  set d := Pr (A ∪ B) - Pr A - Pr B with hd
  have hdne : d ≠ 0 := by rw [hd]; intro hc; apply hne; linarith
  apply h
  refine ⟨3, ![A, B, A ∪ B], ![if 0 < d then -1 else 1, if 0 < d then -1 else 1,
    -(if 0 < d then -1 else 1)], ?_⟩
  intro ω
  rw [payoff_triple]
  have hind : betIndicator (A ∪ B) ω = betIndicator A ω + betIndicator B ω := by
    unfold betIndicator
    by_cases ha : ω ∈ A
    · have hb : ω ∉ B := fun hb => (Finset.disjoint_left.mp hAB ha hb)
      simp [ha, hb, Finset.mem_union]
    · by_cases hb : ω ∈ B <;> simp [ha, hb, Finset.mem_union]
  rw [hind]
  set s := (if 0 < d then (-1 : ℝ) else 1) with hs
  have hexpr : s * (betIndicator A ω - Pr A) + s * (betIndicator B ω - Pr B)
      + (-s) * (betIndicator A ω + betIndicator B ω - Pr (A ∪ B)) = s * d := by
    rw [hd]; ring
  rw [hexpr]
  rcases lt_trichotomy d 0 with hlt | heq | hgt
  · rw [hs, if_neg (by linarith)]; linarith
  · exact absurd heq hdne
  · rw [hs, if_pos hgt]; nlinarith
