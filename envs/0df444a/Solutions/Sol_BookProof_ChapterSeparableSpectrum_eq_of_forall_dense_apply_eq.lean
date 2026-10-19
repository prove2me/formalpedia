-- Prove2me | solution 1 for BookProof.ChapterSeparableSpectrum.eq_of_forall_dense_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:48:25.467659+00:00
-- url     : https://prove2.me/submissions/edcfbfe6-0f00-4fc1-b53f-82be7b5a0e23

-- Generated from ChapterSeparableSpectrum.lean — solution of BookProof.ChapterSeparableSpectrum.eq_of_forall_dense_apply_eq
import Mathlib
import Definitions.Def_ChapterSeparableSpectrum
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
open BookProof.ChapterSeparableSpectrum



noncomputable section

open MeasureTheory TopologicalSpace WeakDual


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianDirectSum
open BookProof.ChapterStandardBorelClassification

variable (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]

set_option maxHeartbeats 1000000 in
theorem solution {D : Set C(Y, ℂ)} (hD : Dense D) {y₁ y₂ : Y}
    (h : ∀ d ∈ D, (d : C(Y, ℂ)) y₁ = d y₂) : y₁ = y₂ := by

  have hsep : ∀ f : C(Y, ℂ), f y₁ = f y₂ := by
    intro f
    have key : ∀ ε : ℝ, 0 < ε → dist (f y₁) (f y₂) < 2 * ε := by
      intro ε hε
      obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.1 (hD f) ε hε
      have h1 : dist (f y₁) (d y₁) < ε :=
        lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist y₁) hd
      have h2 : dist (f y₂) (d y₂) < ε :=
        lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist y₂) hd
      calc dist (f y₁) (f y₂) ≤ dist (f y₁) (d y₁) + dist (d y₂) (f y₂) := by
            rw [h d hdD]; exact dist_triangle _ _ _
        _ < ε + ε := by rw [dist_comm (d y₂)]; exact add_lt_add h1 h2
        _ = 2 * ε := by ring
    have hle : dist (f y₁) (f y₂) ≤ 0 := by
      by_contra hlt
      push_neg at hlt
      have := key (dist (f y₁) (f y₂) / 4) (by linarith)
      linarith
    exact dist_eq_zero.1 (le_antisymm hle dist_nonneg)
  by_contra hne
  obtain ⟨g, hg0, hg1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := y₁)) (isClosed_singleton (x := y₂))
    (by simpa [Set.disjoint_singleton] using hne)
  have := hsep (ContinuousMap.mk (fun y => (g y : ℂ)) (by fun_prop))
  simp [hg0 rfl, hg1 rfl] at this
