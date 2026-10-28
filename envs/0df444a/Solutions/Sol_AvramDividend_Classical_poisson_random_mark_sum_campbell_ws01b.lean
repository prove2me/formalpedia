-- Prove2me | solution 1 for AvramDividend.Classical.poisson_random_mark_sum_campbell_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:11:52.496735+00:00
-- url     : https://prove2.me/submissions/c6f930ed-aa35-4324-8b94-fd22e5d1810e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_independent_count_cell_mark_mean_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real Finset Set
open scoped NNReal ENNReal Nat

/-- Campbell's expected random-mark sum for a genuine Poisson count:
the random sum is integrable, and its expectation is intensity times
mean mark. Both claims follow from count-law, mark-law and independence. -/
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
    (∫ ω, ∑ n ∈ Finset.range (K ω), f (Y n ω) ∂μ) =
      (r : ℝ) * ∫ y, f y ∂ν := by
  classical
  let g : Ω → ℝ := fun ω =>
    ∑ n ∈ Finset.range (K ω), f (Y n ω)
  let s : ℕ → Set Ω := fun j => {ω | K ω = j}
  have hs_meas (j : ℕ) : MeasurableSet (s j) :=
    hKm (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, s, Set.mem_setOf_eq]
    intro ω h1 h2
    exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω =>
      Set.mem_iUnion.2 ⟨K ω, rfl⟩
  have hcell (j : ℕ) :
      Set.EqOn g (fun ω => ∑ n ∈ Finset.range j, f (Y n ω))
        (s j) := by
    intro ω hω
    change K ω = j at hω
    exact congrArg
      (fun c : ℕ => ∑ n ∈ Finset.range c, f (Y n ω)) hω
  have hcount (j : ℕ) :
      μ.real (s j) = (poissonMeasure r).real {j} := by
    have h : μ (s j) = poissonMeasure r {j} := by
      rw [show s j = K ⁻¹' {j} from rfl,
        ← Measure.map_apply hKm (measurableSet_singleton j),
        hKlaw.map_eq]
    rw [measureReal_def, h, ← measureReal_def]
  have hFixedInt (g₀ : E → ℝ) (hg : Measurable g₀)
      (hgi : Integrable g₀ ν) (j : ℕ) :
      Integrable (fun ω => ∑ n ∈ Finset.range j, g₀ (Y n ω)) μ := by
    refine integrable_finsetSum _ fun n hn => ?_
    have hI : Integrable g₀ (Measure.map (Y n) μ) := by
      rwa [(hYL n).map_eq]
    exact hI.comp_measurable (hYm n)
  have hi (j : ℕ) : IntegrableOn g (s j) μ :=
    ((hFixedInt f hf hfI j).integrableOn).congr_fun
      (hcell j).symm (hs_meas j)
  have hmass :
      HasSum (fun n : ℕ => (poissonMeasure r).real {n}) 1 := by
    simpa only [poissonMeasure_real_singleton] using
      hasSum_one_poissonMeasure r
  have hshift (n : ℕ) :
      ((n + 1 : ℕ) : ℝ) * (poissonMeasure r).real {n + 1} =
        (r : ℝ) * (poissonMeasure r).real {n} := by
    simp only [poissonMeasure_real_singleton,
      Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp
  have hPoisson :
      HasSum (fun n : ℕ => (n : ℝ) *
        (poissonMeasure r).real {n}) (r : ℝ) := by
    apply (hasSum_nat_add_iff' 1).mp
    simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    simp_rw [hshift]
    simpa [mul_one] using hmass.mul_left (r : ℝ)
  have hbound (j : ℕ) :
      ∫ ω in s j, ‖g ω‖ ∂μ ≤
        (poissonMeasure r).real {j} *
          ((j : ℝ) * ∫ y, |f y| ∂ν) := by
    have hmono :
        (∫ ω in s j, ‖g ω‖ ∂μ) ≤
          (∫ ω in s j,
            ∑ n ∈ Finset.range j, |f (Y n ω)| ∂μ) := by
      refine setIntegral_mono_on (hi j).norm
        ((hFixedInt (fun y => |f y|) hf.abs hfI.abs j).integrableOn)
        (hs_meas j) ?_
      intro ω hω
      rw [Real.norm_eq_abs, hcell j hω]
      exact Finset.abs_sum_le_sum_abs _ _
    calc
      (∫ ω in s j, ‖g ω‖ ∂μ) ≤
          (∫ ω in s j,
            ∑ n ∈ Finset.range j, |f (Y n ω)| ∂μ) := hmono
      _ = μ.real (s j) *
            ((j : ℝ) * ∫ y, |f y| ∂ν) := by
          simpa only [s] using
            (AvramDividend.Classical.poisson_independent_count_cell_mark_mean_ws01b
              μ ν K Y hKm hYm hYL hIndep j
              (fun y => |f y|) hf.abs hfI.abs)
      _ = (poissonMeasure r).real {j} *
            ((j : ℝ) * ∫ y, |f y| ∂ν) := by rw [hcount j]
  have hsummable :
      Summable (fun j => ∫ ω in s j, ‖g ω‖ ∂μ) := by
    refine Summable.of_nonneg_of_le
      (fun j => integral_nonneg fun _ => norm_nonneg _) hbound ?_
    have h := (hPoisson.summable).mul_left (∫ y, |f y| ∂ν)
    refine h.congr fun j => ?_
    ring
  have hInt : Integrable g μ := by
    have h := integrableOn_iUnion_of_summable_integral_norm hi hsummable
    rwa [hunion, integrableOn_univ] at h
  have hval := integral_iUnion hs_meas hs_disj
    (by rw [hunion]; exact hInt.integrableOn)
  rw [hunion, setIntegral_univ] at hval
  have hcellf (j : ℕ) :
      (∫ ω in s j, g ω ∂μ) =
        (poissonMeasure r).real {j} *
          ((j : ℝ) * ∫ y, f y ∂ν) := by
    calc
      (∫ ω in s j, g ω ∂μ) =
          ∫ ω in s j, ∑ n ∈ Finset.range j, f (Y n ω) ∂μ :=
            setIntegral_congr_fun (hs_meas j) (hcell j)
      _ = μ.real (s j) *
            ((j : ℝ) * ∫ y, f y ∂ν) := by
          simpa only [s] using
            (AvramDividend.Classical.poisson_independent_count_cell_mark_mean_ws01b
              μ ν K Y hKm hYm hYL hIndep j f hf hfI)
      _ = (poissonMeasure r).real {j} *
            ((j : ℝ) * ∫ y, f y ∂ν) := by rw [hcount j]
  calc
    (∫ ω, ∑ n ∈ Finset.range (K ω), f (Y n ω) ∂μ) =
        ∑' j, ∫ ω in s j, g ω ∂μ := hval
    _ = ∑' j, (poissonMeasure r).real {j} *
          ((j : ℝ) * ∫ y, f y ∂ν) :=
        tsum_congr hcellf
    _ = (∫ y, f y ∂ν) * (r : ℝ) := by
      have heq :
          (fun j : ℕ => (poissonMeasure r).real {j} *
            ((j : ℝ) * ∫ y, f y ∂ν)) =
          (fun j : ℕ => (∫ y, f y ∂ν) *
            ((j : ℝ) * (poissonMeasure r).real {j})) := by
        funext j
        ring
      rw [heq, (hPoisson.mul_left (∫ y, f y ∂ν)).tsum_eq]
    _ = (r : ℝ) * ∫ y, f y ∂ν := by ring
