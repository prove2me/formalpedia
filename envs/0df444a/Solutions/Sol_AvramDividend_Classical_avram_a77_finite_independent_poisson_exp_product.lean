-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_finite_independent_poisson_exp_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:36:51.199023+00:00
-- url     : https://prove2.me/submissions/da23f9ca-56e0-466b-85bc-1da50fdaae5c

/- Finite independent Poisson weighted count exponential product.
   Original Avram a77 finite-simple spatial Poisson mark stepping stone.
   The only imported external result is the remotely Proved general
   Poisson PGF; full source spatial independence remains a separate
   genuine OPEN premise on the physical marked jump measure. -/
import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ)
    (N : Fin n → Ω → ℕ)
    (hMeas : ∀ i, Measurable (N i))
    (hIndep : iIndepFun N P)
    (r : Fin n → ℝ≥0)
    (hLaw : ∀ i, HasLaw (N i) (poissonMeasure (r i)) P)
    (a : Fin n → ℝ) :
    (∫ ω, ∏ i, (Real.exp (a i)) ^ N i ω ∂P) =
      ∏ i, Real.exp ((r i : ℝ) * (Real.exp (a i) - 1)) := by
  let f : Fin n → ℕ → ℝ := fun i k => Real.exp (a i) ^ k
  have hf : ∀ i, AEStronglyMeasurable (f i) (P.map (N i)) := by
    intro i
    exact (measurable_of_countable (f i)).aestronglyMeasurable
  have hprod :
      (∫ ω, ∏ i, f i (N i ω) ∂P) =
        ∏ i, (∫ ω, f i (N i ω) ∂P) :=
    hIndep.integral_fun_prod_comp
      (fun i => (hMeas i).aemeasurable) hf
  change (∫ ω, ∏ i, f i (N i ω) ∂P) =
    ∏ i, Real.exp ((r i : ℝ) * (Real.exp (a i) - 1))
  rw [hprod]
  apply Finset.prod_congr rfl
  intro i hi
  have hmap : P.map (N i) = poissonMeasure (r i) :=
    (hLaw i).map_eq
  calc
    (∫ ω, f i (N i ω) ∂P) =
        (∫ k : ℕ, f i k ∂P.map (N i)) := by
      rw [integral_map (hMeas i).aemeasurable (hf i)]
    _ = Real.exp ((r i : ℝ) * (Real.exp (a i) - 1)) := by
      rw [hmap]
      exact chat06_poisson_count_pgf_general (r i) (Real.exp (a i))
