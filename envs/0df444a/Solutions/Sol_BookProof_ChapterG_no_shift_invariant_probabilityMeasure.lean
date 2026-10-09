-- Prove2me | solution 1 for BookProof.ChapterG.no_shift_invariant_probabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:17:29.449243+00:00
-- url     : https://prove2.me/submissions/85589f6f-45f8-4916-ad34-7d8366b502bd

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.no_shift_invariant_probabilityMeasure
import Mathlib
import Definitions.Def_ChapterG
open MeasureTheory
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ ∃ μ : Measure ℤ, IsProbabilityMeasure μ ∧
      ∀ s : Set ℤ, μ ((· + 1) ⁻¹' s) = μ s := by

  rintro ⟨μ, hμ, hinv⟩
  have hpre : ∀ k : ℤ, (· + 1) ⁻¹' ({k} : Set ℤ) = {k - 1} := by
    intro k; ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff]; omega
  have hstep : ∀ k : ℤ, μ {k - 1} = μ {k} := by
    intro k; rw [← hpre k]; exact hinv {k}
  have hconst : ∀ k : ℤ, μ {k} = μ {(0:ℤ)} := by
    intro k
    induction k using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [← hstep ((n:ℤ) + 1)]; simpa using ih
    | pred n ih => rw [hstep (-(n:ℤ))]; simpa using ih
  have huniv : (⋃ k : ℤ, ({k} : Set ℤ)) = Set.univ := by
    ext x; simp
  have hcount : μ Set.univ = ∑' k : ℤ, μ {k} := by
    rw [← huniv, measure_iUnion (fun i j hij => Set.disjoint_singleton.mpr hij)
      (fun k => measurableSet_singleton k)]
  rw [measure_univ] at hcount
  simp only [hconst] at hcount
  by_cases hc : μ {(0:ℤ)} = 0
  · rw [hc] at hcount; simp at hcount
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero hc] at hcount
    exact ENNReal.one_ne_top hcount
