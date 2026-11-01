-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_poisson_random_mark_sum_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:33:57.032995+00:00
-- url     : https://prove2.me/submissions/ea70ef61-7aad-4478-94c3-216e663b4af8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_count_cell_l2_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_uncentred_second_pmf_hasSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- The Poisson number of independent L² marks has an integrable square. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 ν) :
    Integrable (fun ω =>
      (∑ n ∈ Finset.range (K ω), f (Y n ω)) ^ 2) μ := by
  let g : Ω → ℝ := fun ω => (∑ n ∈ Finset.range (K ω), f (Y n ω)) ^ 2
  let s : ℕ → Set Ω := fun j => {ω | K ω = j}
  have hs_meas (j : ℕ) : MeasurableSet (s j) := hKm (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, s, Set.mem_setOf_eq]
    intro ω h1 h2
    exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K ω, rfl⟩
  have hcell (j : ℕ) :
      Set.EqOn g (fun ω => (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2) (s j) := by
    intro ω hω
    change K ω = j at hω
    exact congrArg (fun c : ℕ => (∑ n ∈ Finset.range c, f (Y n ω)) ^ 2) hω
  have hXi (n : ℕ) : MemLp (fun ω => f (Y n ω)) 2 μ := by
    simpa [Function.comp_def] using
      hf2.comp_measurePreserving ((hYL n).measurePreserving (hYm n))
  have hFixedI (j : ℕ) :
      Integrable (fun ω => (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2) μ := by
    have hLp : MemLp (fun ω => ∑ n ∈ Finset.range j, f (Y n ω)) 2 μ :=
      memLp_finset_sum (Finset.range j) (fun n hn => hXi n)
    have hm : Measurable (fun ω => ∑ n ∈ Finset.range j, f (Y n ω)) := by
      apply Finset.measurable_sum
      intro n hn
      exact hf.comp (hYm n)
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).1 hLp
  have hi (j : ℕ) : IntegrableOn g (s j) μ :=
    ((hFixedI j).integrableOn).congr_fun (hcell j).symm (hs_meas j)
  have hCountMass (j : ℕ) :
      μ.real (s j) = (poissonMeasure r).real {j} := by
    have h : μ (s j) = (poissonMeasure r) {j} := by
      rw [show s j = K ⁻¹' {j} from rfl,
        ← Measure.map_apply hKm (measurableSet_singleton j), hKlaw.map_eq]
    rw [measureReal_def, h, ← measureReal_def]
  have hNorm (j : ℕ) :
      (∫ ω in s j, ‖g ω‖ ∂μ) ≤
        (poissonMeasure r).real {j} *
          ((j : ℝ) ^ 2 * ∫ z, f z ^ 2 ∂ν) := by
    have hBound := avram_wave4_p1_marked_count_cell_l2_bound
      μ ν K Y hKm hYm hYL hIndep f hf hf2 j
    have hEq : (∫ ω in s j, ‖g ω‖ ∂μ) =
        (∫ ω in s j, (∑ n ∈ Finset.range j, f (Y n ω)) ^ 2 ∂μ) := by
      apply setIntegral_congr_fun (hs_meas j)
      intro ω hω
      change K ω = j at hω
      simp only [g, Real.norm_of_nonneg (sq_nonneg _)]
      rw [hω]
    rw [hEq]
    simpa only [s, hCountMass j] using hBound
  have hsummable : Summable (fun j => ∫ ω in s j, ‖g ω‖ ∂μ) := by
    refine Summable.of_nonneg_of_le
      (fun j => integral_nonneg fun _ => norm_nonneg _) hNorm ?_
    have h := (avram_wave4_p1_poisson_uncentred_second_pmf_hasSum r).summable.mul_left
      (∫ z, f z ^ 2 ∂ν)
    exact h.congr (fun j => by ring)
  have hint := integrableOn_iUnion_of_summable_integral_norm hi hsummable
  rwa [hunion, integrableOn_univ] at hint
