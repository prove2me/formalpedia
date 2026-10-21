-- Prove2me | solution 1 for AvramDividend.Classical.kernel_sum_unique_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:48:10.940708+00:00
-- url     : https://prove2.me/submissions/34c83f60-add1-483e-a879-7cb169465ca9

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (S : ℕ → Set Ω)
    (κs : ℕ → ProbabilityTheory.Kernel Ω ℝ)
    (hpart : ∀ ω : Ω, ∃! n : ℕ, ω ∈ S n)
    (hselector : ∀ (n : ℕ) (ω : Ω),
      κs n ω = if ω ∈ S n then κ ω else (0 : Measure ℝ)) :
    κ = ProbabilityTheory.Kernel.sum κs := by
  apply ProbabilityTheory.Kernel.ext
  intro ω
  apply Measure.ext
  intro A hA
  obtain ⟨n, hn, huniq⟩ := hpart ω
  rw [ProbabilityTheory.Kernel.sum_apply κs ω]
  rw [Measure.sum_apply (fun k => κs k ω) hA]
  have hterm (k : ℕ) :
      (κs k ω) A = if k = n then (κ ω) A else 0 := by
    rw [hselector k ω]
    by_cases heq : k = n
    · subst k
      simp [hn]
    · have hnot : ω ∉ S k := by
        intro hmem
        exact heq (huniq k hmem)
      simp [heq, hnot]
  simp_rw [hterm]
  simp
