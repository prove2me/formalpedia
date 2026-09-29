-- Prove2me | solution 1 for BookProof.ChapterH9.krylov_bestApprox_antitone
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T04:30:44.538415+00:00
-- url     : https://prove2.me/submissions/39e96ddc-bb4d-4912-90b1-5a106f9bf76f

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.krylov_bestApprox_antitone
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem solution (H : E →ₗ[ℂ] E) (v : E) {m n : ℕ} (hmn : m ≤ n) (u : E) :
    ‖u - (krylovSpan H v n).starProjection u‖ ≤ ‖u - (krylovSpan H v m).starProjection u‖ := by
  -- The Krylov flag is monotone: `span {v, Hv, …, H^{m-1}v} ≤ span {v, Hv, …, H^{n-1}v}`.
  have hsub : ({x | ∃ i < m, x = (H ^ i) v} : Set E) ⊆ {x | ∃ i < n, x = (H ^ i) v} := by
    rintro x ⟨i, hi, rfl⟩
    exact ⟨i, lt_of_lt_of_le hi hmn, rfl⟩
  have hle : krylovSpan H v m ≤ krylovSpan H v n := Submodule.span_mono hsub
  -- The projection onto the larger space is the best approximation, so it beats any
  -- competitor in it — in particular the projection onto the smaller space.
  rw [Submodule.starProjection_minimal (U := krylovSpan H v n)]
  refine ciInf_le ?_
    (⟨(krylovSpan H v m).starProjection u,
      hle ((krylovSpan H v m).starProjection_apply_mem u)⟩ : krylovSpan H v n)
  exact ⟨0, Set.forall_mem_range.mpr fun x => norm_nonneg _⟩

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution

#print axioms solution
