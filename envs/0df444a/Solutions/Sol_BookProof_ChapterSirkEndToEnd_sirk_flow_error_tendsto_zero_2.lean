-- Prove2me | solution 2 for BookProof.ChapterSirkEndToEnd.sirk_flow_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T07:45:10.663294+00:00
-- url     : https://prove2.me/submissions/4e595d89-faa5-44b1-9cc9-c4a090a1871d

-- Generated from ChapterSirkEndToEnd.lean — solution of BookProof.ChapterSirkEndToEnd.sirk_flow_error_tendsto_zero
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
import Theorems.Thm_BookProof_ChapterSirkEndToEnd_tendsto_zero_of_le_sirkBound
open BookProof.ChapterSirkEndToEnd











noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution
    {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
    [∀ m, CompleteSpace (G m)]
    (flow : E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, G m →L[ℂ] G m)
    (C Dmin h : ℝ) (hh : 0 < h) (v : E)
    (hbound : ∀ m, ‖flow v - sirkApprox (V m) (psiB m) v‖ ≤ sirkBound C Dmin h ‖v‖ m) :
    Tendsto (fun m => ‖flow v - sirkApprox (V m) (psiB m) v‖) atTop (𝓝 0) := tendsto_zero_of_le_sirkBound _ C Dmin h ‖v‖ hh (fun _ => norm_nonneg _) hbound
