-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.sqf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:16:09.561894+00:00
-- url     : https://prove2.me/submissions/1403beda-d774-4dd3-b5ee-5005912d0de6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (m m' : ℤ) (hm : Squarefree m) (hm' : Squarefree m') (c : ℚ)
    (h : (m : ℚ) = c ^ 2 * m') : m = m' := by
  have e : c * c.den = c.num := Rat.mul_den_eq_num c
  have h1 : (m : ℚ) * (c.den : ℚ) ^ 2 = (c.num : ℚ) ^ 2 * m' := by
    linear_combination (c.den : ℚ) ^ 2 * h + (m' : ℚ) * (c * c.den + c.num) * e
  have h2 : m * (c.den : ℤ) ^ 2 = c.num ^ 2 * m' := by exact_mod_cast h1
  have hcop : IsCoprime c.num (c.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using c.reduced
  have hD : IsUnit (c.den : ℤ) := by
    apply hm'
    have : (c.den : ℤ) * c.den ∣ c.num ^ 2 * m' := ⟨m, by rw [← h2]; ring⟩
    have hc2 : IsCoprime ((c.den : ℤ) * c.den) (c.num ^ 2) := by
      rw [← pow_two]; exact (hcop.symm.pow)
    exact hc2.dvd_of_dvd_mul_left this
  have hN : IsUnit c.num := by
    apply hm
    have : c.num * c.num ∣ m * (c.den : ℤ) ^ 2 := ⟨m', by rw [h2]; ring⟩
    have hc2 : IsCoprime (c.num * c.num) ((c.den : ℤ) ^ 2) := by
      rw [← pow_two]; exact hcop.pow
    exact hc2.dvd_of_dvd_mul_right this
  have hD2 : (c.den : ℤ) ^ 2 = 1 := by
    rcases Int.isUnit_iff.1 hD with h | h <;> rw [h] <;> norm_num
  have hN2 : c.num ^ 2 = 1 := by
    rcases Int.isUnit_iff.1 hN with h | h <;> rw [h] <;> norm_num
  rw [hD2, hN2] at h2
  linarith
end Formalism.HermitianLattices.StabilizerLevels.PfB
