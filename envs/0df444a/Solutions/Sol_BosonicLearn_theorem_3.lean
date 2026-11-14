-- Prove2me | solution 1 for BosonicLearn.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T02:50:26.434829+00:00
-- url     : https://prove2.me/submissions/5a423aa6-ddc8-4a66-ae35-64dc9ebc9075

import Mathlib
import Definitions.Def_BosonicLearn_successProb
import Definitions.Def_BosonicLearn_heterodyneSuccess
import Definitions.Def_BosonicLearn_promiseClass
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_IsPassive
import Theorems.Thm_BosonicLearn_corollary_19
import Theorems.Thm_BosonicLearn_theorem_5
import Theorems.Thm_BosonicLearn_theorem_9
import Theorems.Thm_BosonicLearn_adaptive_scheme_collective
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

/-- The promise class shrinks as the vacuum gap grows: `Σ ⪰ (½ + ν')I` implies `Σ ⪰ (½ + ν)I` for `ν ≤ ν'`. -/
private lemma promiseClass_anti {n : ℕ} {ν ν' : ℝ} (h : ν ≤ ν') :
    promiseClass n ν' ⊆ promiseClass n ν := by
  rintro ρ ⟨μ, S, hG, hS⟩
  refine ⟨μ, S, hG, ?_⟩
  have h1 : S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
      (S - (1 / 2 + ν') • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) +
        (ν' - ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
    rw [sub_add, ← sub_smul]
    congr 2
    ring
  rw [h1]
  exact hS.add (Matrix.PosSemidef.one.smul (sub_nonneg.mpr h))

/-- The probability that a kernel sends a `μ`-distributed input into a set `A` is at most the mass that the
composed law `μ.bind κ` gives to `A`; no measurability of `A` is needed. -/
private lemma lintegral_kernel_le_bind {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (κ : Kernel α β) (A : Set β) :
    ∫⁻ x, κ x A ∂μ ≤ μ.bind κ A := by
  have hT : MeasurableSet (toMeasurable (μ.bind κ) A) := measurableSet_toMeasurable _ _
  calc ∫⁻ x, κ x A ∂μ ≤ ∫⁻ x, κ x (toMeasurable (μ.bind κ) A) ∂μ :=
        lintegral_mono fun x => measure_mono (subset_toMeasurable _ _)
    _ = μ.bind κ (toMeasurable (μ.bind κ) A) :=
        (Measure.bind_apply hT κ.measurable.aemeasurable).symm
    _ = μ.bind κ A := measure_toMeasurable _

theorem solution :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ ν : ℝ, 0 < ν →
        (∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 2 / ε ^ 2 * min (n : ℝ) (1 + 1 / ν)) ∧
          ∃ est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)),
            Measurable est ∧
            ∀ ρ ∈ promiseClass n ν, ENNReal.ofReal (2 / 3) ≤ heterodyneSuccess N est ρ ε) ∧
        (∀ (N : ℕ) (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O)
            (est : Kernel (Fin N → O) (State (Occupation (Fin n)))), IsMarkovKernel est →
          (∀ ρ ∈ promiseClass n ν, ENNReal.ofReal (2 / 3) ≤ successProb S est ρ.coefficients ε) →
          c * ((n : ℝ) ^ 2 / ε ^ 2 * min (n : ℝ) (1 + 1 / ν)) ≤ N) := by
  -- the three results of the paper that the proof combines
  obtain ⟨C19, hC19, h19⟩ := corollary_19 (1 / 3) (by norm_num) (by norm_num)
  obtain ⟨ε5, hε5, c5, hc5, n5, h5⟩ := theorem_5
  obtain ⟨C9, hC9, ε9, hε9, n9, h9⟩ := theorem_9
  refine ⟨min ε5 ε9, lt_min hε5 hε9, max (max n5 n9) 1, min c5 C9 / 2,
    half_pos (lt_min hc5 hC9), C19, hC19, ?_⟩
  intro n hn ε hε hε0 ν hν
  have hn5 : n5 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn9 : n9 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hε5' : ε < ε5 := lt_of_lt_of_le hε0 (min_le_left _ _)
  have hε9' : ε < ε9 := lt_of_lt_of_le hε0 (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · -- sufficiency: Corollary 19 with failure probability 1/3
    obtain ⟨N, hN, est, hest, hsucc⟩ := h19 n ν hν ε hε
    refine ⟨N, hN, est, hest, fun ρ hρ => ?_⟩
    have h := hsucc ρ hρ
    have e : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
    rwa [e] at h
  · -- necessity
    intro N O _ S est hest hsucc
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hq : 0 ≤ (n : ℝ) ^ 2 / ε ^ 2 := by positivity
    have hc5le : min c5 C9 / 2 ≤ c5 / 2 :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hC9le : min c5 C9 / 2 ≤ C9 / 2 :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    rcases le_or_gt ν 1 with hν1 | hν1
    · rcases le_or_gt (1 / (n : ℝ)) ν with hνn | hνn
      · -- `1/n ≤ ν ≤ 1`: Theorem 5 at `ν`
        have key : c5 * ((n : ℝ) ^ 2 / (ν * ε ^ 2)) ≤ N :=
          h5 n hn5 ν hνn hν1 ε hε hε5' N O S est hest (fun ρ hρ _ => hsucc ρ hρ)
        have hmin : min (n : ℝ) (1 + 1 / ν) ≤ 2 / ν := by
          have h1 : 1 ≤ 1 / ν := by rw [le_div_iff₀ hν]; linarith
          have h2 : 2 / ν = 1 / ν + 1 / ν := by ring
          calc min (n : ℝ) (1 + 1 / ν) ≤ 1 + 1 / ν := min_le_right _ _
            _ ≤ 2 / ν := by linarith
        calc min c5 C9 / 2 * ((n : ℝ) ^ 2 / ε ^ 2 * min (n : ℝ) (1 + 1 / ν))
            ≤ c5 / 2 * ((n : ℝ) ^ 2 / ε ^ 2 * (2 / ν)) := by
              apply mul_le_mul hc5le (mul_le_mul_of_nonneg_left hmin hq) _ (by positivity)
              exact mul_nonneg hq (le_min hnpos.le (by positivity))
          _ = c5 * ((n : ℝ) ^ 2 / (ν * ε ^ 2)) := by field_simp
          _ ≤ N := key
      · -- `ν < 1/n`: the class with gap `1/n` is contained in the class with gap `ν`; Theorem 5 at `1/n`
        have h1n : 1 / (n : ℝ) ≤ 1 := by
          rw [div_le_one hnpos]
          exact_mod_cast hn1
        have key : c5 * ((n : ℝ) ^ 2 / (1 / (n : ℝ) * ε ^ 2)) ≤ N :=
          h5 n hn5 (1 / n) le_rfl h1n ε hε hε5' N O S est hest
            (fun ρ hρ _ => hsucc ρ (promiseClass_anti hνn.le hρ))
        calc min c5 C9 / 2 * ((n : ℝ) ^ 2 / ε ^ 2 * min (n : ℝ) (1 + 1 / ν))
            ≤ c5 * ((n : ℝ) ^ 2 / ε ^ 2 * n) := by
              apply mul_le_mul (hc5le.trans (half_le_self hc5.le))
                (mul_le_mul_of_nonneg_left (min_le_left _ _) hq) _ hc5.le
              exact mul_nonneg hq (le_min hnpos.le (by positivity))
          _ = c5 * ((n : ℝ) ^ 2 / (1 / (n : ℝ) * ε ^ 2)) := by field_simp
          _ ≤ N := key
    · -- `ν > 1`: the scheme with its estimator is one collective POVM; Theorem 9
      obtain ⟨E, hE⟩ := adaptive_scheme_collective S est hest
      have key : C9 * ((n : ℝ) ^ 2 / ε ^ 2) ≤ N := by
        refine h9 ν hν ε hε hε9' n hn9 N E (fun ρ hρ _ => ?_)
        refine (hsucc ρ hρ).trans ?_
        unfold successProb collectiveSuccess
        rw [hE ρ]
        exact lintegral_kernel_le_bind _ est _
      have hmin : min (n : ℝ) (1 + 1 / ν) ≤ 2 := by
        have h1 : 1 / ν ≤ 1 := by rw [div_le_one hν]; exact hν1.le
        calc min (n : ℝ) (1 + 1 / ν) ≤ 1 + 1 / ν := min_le_right _ _
          _ ≤ 2 := by linarith
      calc min c5 C9 / 2 * ((n : ℝ) ^ 2 / ε ^ 2 * min (n : ℝ) (1 + 1 / ν))
          ≤ C9 / 2 * ((n : ℝ) ^ 2 / ε ^ 2 * 2) := by
            apply mul_le_mul hC9le (mul_le_mul_of_nonneg_left hmin hq) _ (by positivity)
            exact mul_nonneg hq (le_min hnpos.le (by positivity))
        _ = C9 * ((n : ℝ) ^ 2 / ε ^ 2) := by ring
        _ ≤ N := key
