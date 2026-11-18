-- Prove2me | solution 1 for DiscreteExpectation.discrete_expectation_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:16:17.774934+00:00
-- url     : https://prove2.me/submissions/eef16631-d8b5-4301-95ff-8dca5bc07e56

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F003
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Tactic
import Theorems.Thm_DiscreteExpectation_rsIntegrable_integrator_sum_finset
import Theorems.Thm_DiscreteExpectation_rsIntegral_integrator_sum_finset_eq
import Theorems.Thm_DiscreteExpectation_rsIntegral_identity_step_eq
import Theorems.Thm_rsIntegral_integrator_const_mul_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DiscreteExpectation
open scoped BigOperators Pointwise Interval
noncomputable section

private theorem source_integrable_const_mul {f α : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 ≤ k) (hint : RSIntegrable f α a b) :
    RSIntegrable f (fun x => k * α x) a b :=
  ⟨rsIntegralWitness_integrator_const_mul hk hint⟩

/-- Source step-integrability witness, reconstructed from the published constructor. -/
private theorem source_integrable_identity_step {c a b : ℝ}
    (ha : a < c) (hb : c < b) :
    RSIntegrable (fun x => x) (stepIndicator c) a b :=
  ⟨rsIntegralWitness_identity_step ha hb⟩

theorem solution (m : ℕ) (c p : Fin m → ℝ)
    (a b : ℝ) (hab : a < b)
    (hp : ∀ i, 0 ≤ p i)
    (ha : ∀ i, a < c i)
    (hb : ∀ i, c i < b)
    (h_int : RSIntegrable (fun x => x) (discreteCDF m c p) a b) :
    cdfExpectation a b (discreteCDF m c p) h_int = ∑ i : Fin m, c i * p i := by

  -- 1. Prepare the integrability proofs for each term `p_i * 1_c_i`
  have h_step_int : ∀ i, RSIntegrable (fun x => x) (stepIndicator (c i)) a b :=
    fun i => source_integrable_identity_step (ha i) (hb i)

  have h_mul_int : ∀ i, RSIntegrable (fun x => x) (fun x => p i * stepIndicator (c i) x) a b :=
    fun i => source_integrable_const_mul (hp i) (h_step_int i)

  -- Now we just pass `h_mul_int` cleanly!
  have h_sum_int : RSIntegrable (fun x => x) (fun x => ∑ i : Fin m, p i * stepIndicator (c i) x) a b :=
    rsIntegrable_integrator_sum_finset Finset.univ _ a b hab h_mul_int

  -- 2. Swap the definition using proof irrelevance
  have h_eq : rsIntegral (fun x => x) (discreteCDF m c p) a b h_int =
              rsIntegral (fun x => x) (fun x => ∑ i : Fin m, p i * stepIndicator (c i) x) a b h_sum_int := by
    congr 1

  unfold cdfExpectation
  rw [h_eq]

  -- 3. Apply the finite sum decomposition theorem (passing h_mul_int)
  rw [rsIntegral_integrator_sum_finset_eq Finset.univ _ a b hab h_mul_int]

  -- 4. Dive into the sum and apply constant multiplication & step evaluation
  apply Finset.sum_congr rfl
  intro i _hi

  have H_mul := rsIntegral_integrator_const_mul_eq (hp i) (h_step_int i)
  rw [H_mul]

  have H_step := rsIntegral_identity_step_eq (ha i) (hb i) (h_step_int i)
  rw [H_step]

  ring
