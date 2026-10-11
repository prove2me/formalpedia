-- Prove2me | solution 1 for BookProof.ChapterU.portfolio_risk_inv_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:18.514286+00:00
-- url     : https://prove2.me/submissions/f5fc01dd-542f-4fd3-b72b-3a467c1c2e9c

-- Generated from ChapterU.lean — solution of BookProof.ChapterU.portfolio_risk_inv_sqrt
import Mathlib
import Definitions.Def_ChapterU
open BookProof.ChapterU



open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

variable {X : Type*} [MeasurableSpace X]
variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in

theorem solution {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (σ : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hindep : ProbabilityTheory.iIndepFun X P)
    (hmem : ∀ i, MemLp (X i) 2 P) (hvar : ∀ i, ProbabilityTheory.variance (X i) P = σ ^ 2) :
    ProbabilityTheory.variance (fun ω => (∑ i, X i ω) / n) P = σ ^ 2 / n := by
  have h_var_sum : (ProbabilityTheory.variance (fun ω => ∑ i, X i ω) P) = ∑ i,
      (ProbabilityTheory.variance (X i) P) := by
    convert ProbabilityTheory.IndepFun.variance_sum ( fun i _ => hmem i ) _;
    · simp [ Finset.sum_apply ];
    · intro i _ j _ hij; exact hindep.indepFun hij;
  simp_all [ div_eq_inv_mul, ProbabilityTheory.variance_const_mul ];
  simp [ sq, mul_assoc, hn.ne' ]

/-
Standard-deviation form of `portfolio_risk_inv_sqrt`: the aggregate
standard deviation is `σ/√n`.
-/
