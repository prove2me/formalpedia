-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_random_mark_sum_exact_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:47:57.660954+00:00
-- url     : https://prove2.me/submissions/849cc987-87f7-4233-b9c4-ce845ea72668

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_random_mark_sum_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_count_cell_exact_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_first_pmf_hasSum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_uncentred_second_pmf_hasSum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat
/-- Exact second moment of the genuinely random-length iid marked Poisson sum. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν]
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ) (hYi : iIndepFun Y μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν) :
    (∫ ω, (∑ n ∈ Finset.range (K ω), f (Y n ω)) ^ 2 ∂μ) =
      (r : ℝ) * (∫ z, f z ^ 2 ∂ν) + (r : ℝ) ^ 2 * (∫ z, f z ∂ν) ^ 2 := by
  let g : Ω → ℝ := fun ω => (∑ n ∈ Finset.range (K ω), f (Y n ω)) ^ 2
  let s : ℕ → Set Ω := fun j => {ω | K ω = j}
  let q : ℝ := ∫ z, f z ^ 2 ∂ν; let m : ℝ := ∫ z, f z ∂ν; let p : ℕ → ℝ := fun j => (poissonMeasure r).real {j}
  have hm (j : ℕ) : MeasurableSet (s j) := hKm (measurableSet_singleton j)
  have hd : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, s, Set.mem_setOf_eq]
    intro ω h1 h2
    exact hab (h1 ▸ h2)
  have hu : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K ω, rfl⟩
  have hgi : Integrable g μ :=
    avram_wave4_p1_poisson_random_mark_sum_square_integrable
      μ ν K Y hKm r hKlaw hYm hYL hIndep f hf hf2
  have hcell (j : ℕ) :
      (∫ ω in s j, g ω ∂μ) =
        μ.real (s j) * ((j : ℝ) * q + (j : ℝ) * ((j : ℝ) - 1) * m ^ 2) := by
    have hEq : (∫ ω in s j, g ω ∂μ) =
        (∫ ω in s j, (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 ∂μ) := by
      apply setIntegral_congr_fun (hm j)
      intro ω hω; change K ω = j at hω; simp only [g]; rw [hω]
    rw [hEq]
    simpa only [s, q, m] using
      (avram_wave4_p1_marked_count_cell_exact_second_moment
        μ ν K Y hKm hYm hYL hYi hIndep j f hf hfI hf2)
  have hmass (j : ℕ) : μ.real (s j) = p j := by
    have h : μ (s j) = (poissonMeasure r) {j} := by
      rw [show s j = K ⁻¹' {j} from rfl, ← Measure.map_apply hKm (measurableSet_singleton j), hKlaw.map_eq]
    rw [measureReal_def, h, ← measureReal_def]
  have h1 := avram_wave4_p1_poisson_first_pmf_hasSum r; have h2 := avram_wave4_p1_poisson_uncentred_second_pmf_hasSum r
  have hfac : HasSum
      (fun j : ℕ => ((j : ℝ) * ((j : ℝ) - 1)) * p j) ((r : ℝ) ^ 2) := by
    have hFun : (fun j : ℕ => ((j : ℝ) * ((j : ℝ) - 1)) * p j) = fun j : ℕ => (j : ℝ) ^ 2 * p j - (j : ℝ) * p j := by
      funext j; ring
    have hval : ((r : ℝ) ^ 2 + (r : ℝ)) - (r : ℝ) = (r : ℝ) ^ 2 := by ring
    rw [hFun, ← hval]
    exact h2.sub h1
  have hmix : HasSum
      (fun j : ℕ => p j * ((j : ℝ) * q +
        (j : ℝ) * ((j : ℝ) - 1) * m ^ 2))
      ((r : ℝ) * q + (r : ℝ) ^ 2 * m ^ 2) := by
    have hFun : (fun j : ℕ => p j * ((j : ℝ) * q +
        (j : ℝ) * ((j : ℝ) - 1) * m ^ 2)) =
        fun j : ℕ =>
          q * ((j : ℝ) * p j) + m ^ 2 * (((j : ℝ) * ((j : ℝ) - 1)) * p j) := by
      funext j; ring
    have hval : q * (r : ℝ) + (m ^ 2) * (r : ℝ) ^ 2 =
        (r : ℝ) * q + (r : ℝ) ^ 2 * m ^ 2 := by ring
    rw [hFun, ← hval]
    exact (h1.mul_left q).add (hfac.mul_left (m ^ 2))
  calc
    (∫ ω, g ω ∂μ) = ∑' j, ∫ ω in s j, g ω ∂μ := by
      simpa only [hu, setIntegral_univ] using
        (integral_iUnion hm hd (by simpa only [hu, integrableOn_univ] using hgi))
    _ = ∑' j, p j * ((j : ℝ) * q +
        (j : ℝ) * ((j : ℝ) - 1) * m ^ 2) := by
      apply tsum_congr
      intro j
      rw [hcell j, hmass j]
    _ = (r : ℝ) * q + (r : ℝ) ^ 2 * m ^ 2 := hmix.tsum_eq