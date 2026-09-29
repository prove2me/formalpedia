-- Prove2me | solution 1 for BookProof.StrichartzWave.exists_smooth_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T13:23:30.607797+00:00
-- url     : https://prove2.me/submissions/e8239750-3bc8-4f5a-8b6b-4946e1e29f8b

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.exists_smooth_cutoff
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
omit [MeasurableSpace V] [BorelSpace V] in
theorem solution (R : ℝ) :
    ∃ χ : V → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x, ‖x‖ ≤ R → χ x = 1) ∧ (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, R + 1 ≤ ‖x‖ → χ x = 0) ∧ ∃ C : ℝ, ∀ x, ‖gradient χ x‖ ≤ C := by

  have hs : IsClosed {x : V | R + 1 ≤ ‖x‖} := isClosed_le continuous_const continuous_norm
  have ht : IsClosed (Metric.closedBall (0 : V) R) := Metric.isClosed_closedBall
  have hd : Disjoint {x : V | R + 1 ≤ ‖x‖} (Metric.closedBall (0 : V) R) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_setOf_eq] at hx
    simp only [Metric.mem_closedBall, dist_zero_right] at hx'
    linarith
  obtain ⟨f, hf0, hf1, hfIcc⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (modelWithCornersSelf ℝ V) hs ht hd
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑f) := contMDiff_iff_contDiff.mp f.contMDiff
  have hcs : HasCompactSupport (⇑f) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : V) (R + 1))
    intro x hx
    apply hf0
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    simp only [Set.mem_setOf_eq]
    linarith
  refine ⟨⇑f, hsmooth, hcs, fun x hx => hf1 (by simpa [dist_zero_right] using hx), hfIcc,
    fun x hx => hf0 hx, ?_⟩
  have hgrad : ∀ x : V, gradient (⇑f) x = (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ (⇑f) x) :=
    fun _ => rfl
  have hgcs : HasCompactSupport (fun x => gradient (⇑f) x) := by
    simp only [hgrad]
    exact (hcs.fderiv ℝ).comp_left (g := fun L => (InnerProductSpace.toDual ℝ V).symm L) (by simp)
  have hgcont : Continuous (fun x => gradient (⇑f) x) := by
    simp only [hgrad]
    exact (InnerProductSpace.toDual ℝ V).symm.continuous.comp (hsmooth.continuous_fderiv (by simp))
  exact hgcs.exists_bound_of_continuous hgcont
