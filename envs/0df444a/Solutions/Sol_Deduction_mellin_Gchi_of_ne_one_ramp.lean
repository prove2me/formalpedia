-- Prove2me | solution 1 for Deduction.mellin_Gchi_of_ne_one_ramp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:03.856105+00:00
-- url     : https://prove2.me/submissions/8b07abaa-0fe0-4df8-8e3c-2eb532562d69

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_MellinRamp
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiOfNeOne
import Theorems.Thm_Deduction_mellin_Gchi_of_ne_one_int
import Theorems.Thm_Deduction_mellin_Gchi_of_ne_one_norm
import Theorems.Thm_Deduction_mellin_Gchi_of_ne_one_hasSum
import Theorems.Thm_Deduction_mellin_ramp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (f : ℕ → ℂ) (s : ℂ) (hs : 1 < s.re)
    (hf : LSeriesSummable (fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s)
    (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 1)) :
    ∫ y in Ioi (1 : ℝ), (ramp f y * (y : ℂ) ^ (-s - 1) + g y) =
      LSeries (fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s / (s * (s - 1)) +
        ∫ y in Ioi (1 : ℝ), g y := by
  set a : ℕ → ℂ := fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with ha
  let F : ℕ → ℝ → ℂ := fun n y => match n with
    | 0 => g y
    | m + 1 => a (m + 1) * (((max (y / ((m + 1 : ℕ) : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 1)) := by
    rintro (_ | m)
    · exact hg
    · exact (mellin_Gchi_of_ne_one_int (m + 1) (by omega) s hs).const_mul _
  have hsum : Summable fun n => ∫ y in Ioi (1 : ℝ), ‖F n y‖ := by
    rw [← summable_nat_add_iff 1]
    have h1 := ((summable_nat_add_iff 1).mpr hf.norm).div_const (s.re * (s.re - 1))
    refine h1.congr fun m => ?_
    simp only [F]
    simp_rw [norm_mul (a (m + 1))]
    rw [integral_const_mul, mellin_Gchi_of_ne_one_norm (m + 1) (by omega) s hs,
      LSeries.norm_term_eq, if_neg (by omega), Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hF : ∀ y, ∑' n, F n y = ramp f y * (y : ℂ) ^ (-s - 1) + g y := by
    intro y
    have h1 := (hasSum_nat_add_iff' 1).mpr
      ((mellin_Gchi_of_ne_one_hasSum f y).mul_right ((y : ℂ) ^ (-s - 1)))
    have h2 : HasSum (fun n => F (n + 1) y) (ramp f y * (y : ℂ) ^ (-s - 1)) := by
      convert h1 using 1
      · rfl
      · ext m
        simp only [F, ha]
        ring
      · simp
    have h3 := (hasSum_nat_add_iff (f := fun n => F n y) 1).mp h2
    simpa [F] using h3.tsum_eq
  simp_rw [hF] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr (hf.hasSum.div_const (s * (s - 1)))
  have h2 : HasSum (fun n => ∫ y in Ioi (1 : ℝ), F (n + 1) y) (LSeries a s / (s * (s - 1))) := by
    convert h1 using 1
    · rfl
    · ext m
      simp only [F]
      rw [integral_const_mul, mellin_ramp (m + 1) (by omega) s hs,
        LSeries.term_of_ne_zero (by omega), cpow_neg]
      ring
    · simp [LSeries]
  have h3 := (hasSum_nat_add_iff (f := fun n => ∫ y in Ioi (1 : ℝ), F n y) 1).mp h2
  simpa [F] using h.unique h3
end Deduction
