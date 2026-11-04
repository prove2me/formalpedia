-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_laplace_integer_zero_forces_original_monotone_residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:36:15.377914+00:00
-- url     : https://prove2.me/submissions/2328eac0-26f4-49ab-8070-5746870a58ce

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators

/-- Vanishing bounded exponential deficits at integer clocks force a
nonnegative increasing random clock to vanish at every real time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (R : ℝ≥0 → Ω → ℝ)
    (hzero : ∀ ω : Ω, R 0 ω = 0)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => R t ω))
    (hInt : ∀ n : ℕ, Integrable
      (fun ω => 1 - Real.exp (-(R (n : ℝ≥0) ω))) P)
    (hMean : ∀ n : ℕ,
      (∫ ω, 1 - Real.exp (-(R (n : ℝ≥0) ω)) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, R t ω = 0 := by
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, R (n : ℝ≥0) ω = 0 := by
    intro n
    have hDefNonneg : 0 ≤ᵐ[P]
        (fun ω : Ω => 1 - Real.exp (-(R (n : ℝ≥0) ω))) := by
      filter_upwards [hmono] with ω hmonoω
      have hRpos : 0 ≤ R (n : ℝ≥0) ω := by
        simpa only [hzero ω] using hmonoω
          (show (0 : ℝ≥0) ≤ (n : ℝ≥0) from zero_le)
      have hexp : Real.exp (-(R (n : ℝ≥0) ω)) ≤ 1 :=
        (Real.exp_le_one_iff).mpr (neg_nonpos.mpr hRpos)
      dsimp
      linarith
    have hDefZero : (fun ω : Ω =>
        1 - Real.exp (-(R (n : ℝ≥0) ω))) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hDefNonneg (hInt n)).mp (hMean n)
    filter_upwards [hDefZero] with ω hz
    have hExp : Real.exp (-(R (n : ℝ≥0) ω)) = 1 := by
      have hval : 1 - Real.exp (-(R (n : ℝ≥0) ω)) = 0 := hz
      linarith
    exact neg_eq_zero.mp ((Real.exp_eq_one_iff (-(R (n : ℝ≥0) ω))).mp hExp)
  have hNat : ∀ᵐ ω ∂P, ∀ n : ℕ, R (n : ℝ≥0) ω = 0 :=
    ae_all_iff.mpr hn
  filter_upwards [hmono, hNat] with ω hmonoω hω
  intro t
  obtain ⟨n, htn⟩ := exists_nat_ge (t : ℝ)
  have htn' : t ≤ (n : ℝ≥0) := by exact_mod_cast htn
  have hlow : 0 ≤ R t ω := by
    calc 0 = R 0 ω := (hzero ω).symm
         _ ≤ R t ω := hmonoω (show (0 : ℝ≥0) ≤ t from zero_le)
  have hhigh : R t ω ≤ 0 := by
    calc R t ω ≤ R (n : ℝ≥0) ω := hmonoω htn'
         _ = 0 := hω n
  exact le_antisymm hhigh hlow
