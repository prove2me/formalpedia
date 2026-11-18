-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_joint_marked_count_pgf_hasSum_exact_count_cell_coefficients_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:51:30.873229+00:00
-- url     : https://prove2.me/submissions/e61c6fca-5a21-4585-b7c6-eec7c1431f94

import Theorems.Thm_AvramDividend_Classical_avram_a27_integral_eq_hasSum_exact_nat_count_cell_integrals_20261117
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- The joint marked count PGF is the exact count-cell power series, without any independent mark construction. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (hK : Measurable K)
    (F : Ω → ℝ) (z : ℝ)
    (hInt : Integrable (fun ω => z ^ (K ω) * F ω) P) :
    HasSum (fun k : ℕ => z ^ k *
      (∫ ω in {ω : Ω | K ω = k}, F ω ∂P))
      (∫ ω, z ^ (K ω) * F ω ∂P) := by
  classical
  have hBase :=
    avram_a27_integral_eq_hasSum_exact_nat_count_cell_integrals_20261117
      P K hK (fun ω => z ^ (K ω) * F ω) hInt
  have hCoeff (k : ℕ) :
      (∫ ω in {ω : Ω | K ω = k}, z ^ (K ω) * F ω ∂P) =
      z ^ k * (∫ ω in {ω : Ω | K ω = k}, F ω ∂P) := by
    calc
      (∫ ω in {ω : Ω | K ω = k}, z ^ (K ω) * F ω ∂P) =
          ∫ ω in {ω : Ω | K ω = k}, z ^ k * F ω ∂P := by
            apply setIntegral_congr_fun ((measurableSet_singleton k).preimage hK)
            intro ω hω
            change z ^ (K ω) * F ω = z ^ k * F ω
            rw [hω]
      _ = z ^ k * (∫ ω in {ω : Ω | K ω = k}, F ω ∂P) := by
            exact integral_const_mul (z ^ k) F
  have heq :
      (fun k : ℕ => z ^ k * (∫ ω in {ω : Ω | K ω = k}, F ω ∂P)) =
      (fun k : ℕ => ∫ ω in {ω : Ω | K ω = k}, z ^ (K ω) * F ω ∂P) := by
    funext k
    exact (hCoeff k).symm
  rw [heq]
  exact hBase
