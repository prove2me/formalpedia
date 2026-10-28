-- Prove2me | solution 1 for AvramDividend.Classical.poisson_random_mark_sum_integrable_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:21:55.934285+00:00
-- url     : https://prove2.me/submissions/bc3380e4-a66c-409a-b392-1d738ee3cc5d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_mark_sum_cell_absolute_integral_bound_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- Actual Poisson-prefix marked sums are integrable for L1 marks. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν) :
    Integrable (fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω)) μ := by
  let g : Ω → ℝ := fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω)
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
      Set.EqOn g (fun ω => ∑ n ∈ Finset.range j, f (Y n ω))
        (s j) := by
    intro ω hω
    change K ω = j at hω
    exact congrArg (fun c : ℕ => ∑ n ∈ Finset.range c, f (Y n ω)) hω
  have hFixed (j : ℕ) :
      Integrable (fun ω => ∑ n ∈ Finset.range j, f (Y n ω)) μ := by
    refine integrable_finsetSum _ fun n hn => ?_
    have hm : Integrable f (Measure.map (Y n) μ) := by
      rwa [(hYL n).map_eq]
    exact hm.comp_measurable (hYm n)
  have hi (j : ℕ) : IntegrableOn g (s j) μ :=
    ((hFixed j).integrableOn).congr_fun (hcell j).symm (hs_meas j)
  have hmass : HasSum (fun n : ℕ => (poissonMeasure r).real {n}) 1 := by
    simpa only [poissonMeasure_real_singleton] using hasSum_one_poissonMeasure r
  have hshift (n : ℕ) :
      ((n + 1 : ℕ) : ℝ) * (poissonMeasure r).real {n + 1} =
        (r : ℝ) * (poissonMeasure r).real {n} := by
    simp only [poissonMeasure_real_singleton,
      Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp
  have hPoisson :
      HasSum (fun n : ℕ => (n : ℝ) * (poissonMeasure r).real {n}) (r : ℝ) := by
    apply (hasSum_nat_add_iff' 1).mp
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    simp_rw [hshift]
    simpa [mul_one] using hmass.mul_left (r : ℝ)
  have hNorm (j : ℕ) :
      (∫ ω in s j, ‖g ω‖ ∂μ) ≤
        (poissonMeasure r).real {j} * ((j : ℝ) * ∫ y, |f y| ∂ν) := by
    have hcellBound :=
      poisson_mark_sum_cell_absolute_integral_bound_ws01b
        μ ν K Y hKm hYm hYL hIndep j f hf hfI
    have hcount : μ.real (s j) =
        (poissonMeasure r).real {j} := by
      have h : μ (s j) = (poissonMeasure r) {j} := by
        rw [show s j = K ⁻¹' {j} from rfl,
          ← Measure.map_apply hKm (measurableSet_singleton j),
          hKlaw.map_eq]
      rw [measureReal_def, h, ← measureReal_def]
    simpa [s, g, Real.norm_eq_abs, hcount] using hcellBound
  have hsummable :
      Summable (fun j => ∫ ω in s j, ‖g ω‖ ∂μ) := by
    refine Summable.of_nonneg_of_le
      (fun j => integral_nonneg fun _ => norm_nonneg _) hNorm ?_
    have h := hPoisson.summable.mul_left (∫ y, |f y| ∂ν)
    refine h.congr fun j => ?_
    ring
  have hint := integrableOn_iUnion_of_summable_integral_norm hi hsummable
  rwa [hunion, integrableOn_univ] at hint
