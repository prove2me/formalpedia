-- Prove2me | solution 1 for BookProof.NonnegResolvent.tendsto_smul_resAt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:28:28.508043+00:00
-- url     : https://prove2.me/submissions/67429b7d-4527-4480-a229-28933ff18172

import Definitions.Def_ChapterNonnegResolvent

open BookProof.ClosureUniqueness
open scoped ComplexOrder
open BookProof.PositiveSquareRoot
open BookProof.NonnegResolvent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T : Submodule ℂ (F × F)} {a b : ℝ}

theorem solution (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (h : F) :
    Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) • resAt hT n h) Filter.atTop
      (nhds h) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A, hA, hbound⟩ := tendsto_smul_invCLMAt hT hsv h hε
  refine ⟨⌈A⌉₊, fun n hn => ?_⟩
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hAc : A ≤ (n : ℝ) + 1 := by
    have h1 : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have h2 : ((⌈A⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [dist_eq_norm]
  exact hbound ((n : ℝ) + 1) hc hAc
