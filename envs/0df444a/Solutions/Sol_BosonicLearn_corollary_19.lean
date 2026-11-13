-- Prove2me | solution 1 for BosonicLearn.corollary_19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T03:35:23.253408+00:00
-- url     : https://prove2.me/submissions/f19a677a-3287-430e-b9e1-4861f1bd2a11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneSuccess
import Definitions.Def_BosonicLearn_promiseClass
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicLearn_traceDist
import Theorems.Thm_BosonicLearn_theorem_8
import Theorems.Thm_BosonicLearn_bmem25_theorem_10
import Theorems.Thm_BosonicLearn_traceDist_le_one
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

/-- A state of the promise class with gap `ν > 0` has `Σ ≻ ½ I`:
`Σ − ½I = (Σ − (½ + ν)I) + νI` is positive semidefinite plus positive definite. -/
private lemma promiseClass_posDef {n : ℕ} {ν : ℝ} (hν : 0 < ν) {ρ : State (Occupation (Fin n))}
    (hρ : ρ ∈ promiseClass n ν) :
    ∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
      IsGaussianState ρ μ S ∧
        (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosDef := by
  obtain ⟨μ, S, hG, hS⟩ := hρ
  refine ⟨μ, S, hG, ?_⟩
  have h1 : S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
      (S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) +
        ν • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
    rw [add_smul]
    abel
  rw [h1]
  exact Matrix.PosDef.posSemidef_add hS (Matrix.PosDef.one.smul hν)

/-- With no samples and a constant estimate `σ`, every state is learned to accuracy `ϵ ≥ 1` with probability
one, because the trace distance of two states is at most one. -/
private lemma heterodyneSuccess_zero_const {n : ℕ} (σ ρ : State (Occupation (Fin n))) {ϵ : ℝ}
    (hϵ : 1 ≤ ϵ) :
    heterodyneSuccess 0 (fun _ => σ) ρ ϵ = 1 := by
  unfold heterodyneSuccess
  rw [Measure.pi_of_empty]
  exact Measure.dirac_apply_of_mem
    ((traceDist_le_one σ ρ).trans (ENNReal.one_le_ofReal.mpr hϵ))

theorem solution :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : ℝ), 0 < ν → ∀ ϵ : ℝ, 0 < ϵ →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 2 / ϵ ^ 2 * min (n : ℝ) (1 + 1 / ν)) ∧
        ∃ est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)),
          Measurable est ∧
          ∀ ρ ∈ promiseClass n ν, ENNReal.ofReal (1 - δ) ≤ heterodyneSuccess N est ρ ϵ := by
  intro δ hδ0 hδ1
  obtain ⟨C8, hC8, h8⟩ := theorem_8
  obtain ⟨C10, hC10, h10⟩ := bmem25_theorem_10 δ hδ0 hδ1
  have hL : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    linarith
  have hC8L : 0 < C8 * (1 + Real.log (1 / δ)) := mul_pos hC8 (by linarith)
  have hCpos : 0 < C10 + C8 * (1 + Real.log (1 / δ)) := add_pos hC10 hC8L
  refine ⟨C10 + C8 * (1 + Real.log (1 / δ)), hCpos, ?_⟩
  intro n ν hν ϵ hϵ
  have h1ν : 0 < 1 + 1 / ν := by positivity
  have hq : 0 ≤ (n : ℝ) ^ 2 / ϵ ^ 2 := by positivity
  rcases le_or_gt 1 ϵ with hϵ1 | hϵ1
  · -- `ϵ ≥ 1`: no sample is needed, any fixed state is within trace distance `1 ≤ ϵ`
    obtain ⟨N', -, est', -, -⟩ := h10 n 1 one_pos
    refine ⟨0, ?_, fun _ => est' (fun _ => 0), measurable_const, fun ρ _ => ?_⟩
    · have hf : 0 ≤ (n : ℝ) ^ 2 / ϵ ^ 2 * min (n : ℝ) (1 + 1 / ν) :=
        mul_nonneg hq (le_min (Nat.cast_nonneg n) h1ν.le)
      simpa using mul_nonneg hCpos.le hf
    · rw [heterodyneSuccess_zero_const _ ρ hϵ1]
      exact ENNReal.ofReal_le_one.mpr (by linarith)
  · rcases le_or_gt (n : ℝ) (1 + 1 / ν) with hcase | hcase
    · -- `ϵ < 1`, `n ≤ 1 + 1/ν`: the general heterodyne bound of [BMEM25, Theorem 10]
      obtain ⟨N, hN, est, hest, hsucc⟩ := h10 n ϵ hϵ
      refine ⟨N, ?_, est, hest, fun ρ hρ => hsucc ρ (promiseClass_posDef hν hρ)⟩
      rw [min_eq_left hcase]
      calc (N : ℝ) ≤ C10 * ((n : ℝ) ^ 3 / ϵ ^ 2) := hN
        _ = C10 * ((n : ℝ) ^ 2 / ϵ ^ 2 * n) := by ring
        _ ≤ (C10 + C8 * (1 + Real.log (1 / δ))) * ((n : ℝ) ^ 2 / ϵ ^ 2 * n) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hq (Nat.cast_nonneg n))
    · -- `ϵ < 1`, `1 + 1/ν < n`: Theorem 8
      obtain ⟨N, hN, est, hest, -, hsucc⟩ := h8 n ν hν ϵ δ hϵ hϵ1 hδ0 hδ1
      refine ⟨N, ?_, est, hest, hsucc⟩
      rw [min_eq_right hcase.le]
      have hn1 : (1 : ℝ) ≤ n := by
        have h := one_div_pos.mpr hν
        linarith
      have hstep : (n : ℝ) * (n + Real.log (1 / δ)) ≤ (1 + Real.log (1 / δ)) * (n : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg hL (Nat.cast_nonneg n)) (sub_nonneg.mpr hn1)]
      calc (N : ℝ) ≤ C8 * ((1 + 1 / ν) * ((n : ℝ) * (n + Real.log (1 / δ))) / ϵ ^ 2) := hN
        _ ≤ C8 * ((1 + 1 / ν) * ((1 + Real.log (1 / δ)) * (n : ℝ) ^ 2) / ϵ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hstep h1ν.le) (by positivity))
              hC8.le
        _ = C8 * (1 + Real.log (1 / δ)) * ((n : ℝ) ^ 2 / ϵ ^ 2 * (1 + 1 / ν)) := by ring
        _ ≤ (C10 + C8 * (1 + Real.log (1 / δ))) * ((n : ℝ) ^ 2 / ϵ ^ 2 * (1 + 1 / ν)) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hq h1ν.le)
