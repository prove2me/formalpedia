-- Prove2me | solution 1 for Brouwer.exists_contDiff_approx_real
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:09.683265+00:00
-- url     : https://prove2.me/submissions/c5e4eb74-3150-4872-a50a-9182fece5d72

import Mathlib

open Metric Set MeasureTheory

-- carved verbatim out of submission 08ed2756-557a-470f-8493-8c93e6b779c8, lines 543-579


theorem solution {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContinuousOn φ (closedBall 0 1)) (η : ℝ) (hη : 0 < η) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |G x - φ x| < η := by
  set B : Set (EuclideanSpace ℝ (Fin d)) := closedBall 0 1 with hB
  have : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let A : Subalgebra ℝ C(B, ℝ) :=
    { carrier := {g | ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧ ∀ x : B, g x = G x}
      mul_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x * Gb x, hGa.mul hGb, fun x => by simp [ha, hb]⟩
      add_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x + Gb x, hGa.add hGb, fun x => by simp [ha, hb]⟩
      algebraMap_mem' := fun r => ⟨fun _ => r, contDiff_const, fun x => by simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have : ∃ i, (x : EuclideanSpace ℝ (Fin d)) i ≠ (y : EuclideanSpace ℝ (Fin d)) i := by
      by_contra h
      push Not at h
      apply hxy
      apply Subtype.ext
      ext i
      exact h i
    obtain ⟨i, hi⟩ := this
    refine ⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, ?_, hi⟩
    refine ⟨⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, by fun_prop⟩, ?_, rfl⟩
    exact ⟨fun z => z i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff,
      fun z => rfl⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hsep
    (fun x : B => φ x) hφ.domRestrict η hη
  obtain ⟨G, hG, hgG⟩ := g.2
  refine ⟨G, hG, fun x hx => ?_⟩
  have := hg ⟨x, hx⟩
  rw [Real.norm_eq_abs] at this
  simpa [hgG] using this
