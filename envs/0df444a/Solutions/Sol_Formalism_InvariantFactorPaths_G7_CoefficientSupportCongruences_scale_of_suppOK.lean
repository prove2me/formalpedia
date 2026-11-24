-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.scale_of_suppOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:28:02.677194+00:00
-- url     : https://prove2.me/submissions/f8906730-9a9c-40c7-afb5-41fd07169ea9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_LT_InvIntP_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
namespace CoefficientSupportCongruences
open FrobeniusSubstitution
section Supp
variable {K : Type} [Field K]
private theorem coeff_subst_C_mul_X_eq_mul_coeff (a : Fin 2 → K) (G : MvPowerSeries (Fin 2) K)
    (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n
        (MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) G) =
      (a 0 ^ n 0 * a 1 ^ n 1) * MvPowerSeries.coeff n G := by
  have e : (fun s => MvPowerSeries.C (a s) * (MvPowerSeries.X s : MvPowerSeries (Fin 2) K)) =
      a • MvPowerSeries.X := by
    funext s
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [e, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
end Supp
end CoefficientSupportCongruences
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
theorem _root_.solution {p : ℕ} {G : MvPowerSeries (Fin 2) K} (hG : SuppOK p G) {ζ : K}
    (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    MvPowerSeries.subst ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 :
        MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G =
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] G := by
  have eL : ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1] = fun s => MvPowerSeries.C (![ζ, 1] s) * MvPowerSeries.X s := by
    funext s; fin_cases s <;> simp
  have eR : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] =
      fun s => MvPowerSeries.C (![1, ζ ^ p] s) * MvPowerSeries.X s := by
    funext s; fin_cases s <;> simp
  rw [eL, eR]
  ext n
  rw [coeff_subst_C_mul_X_eq_mul_coeff, coeff_subst_C_mul_X_eq_mul_coeff]
  by_cases h : MvPowerSeries.coeff n G = 0
  · simp [h]
  · obtain ⟨-, -, hmod⟩ := hG n h
    have hmod' : n 0 % (p ^ 2 - 1) = (p * n 1) % (p ^ 2 - 1) := hmod
    have key : ζ ^ n 0 = (ζ ^ p) ^ n 1 := by
      rw [← pow_mul, pow_eq_pow_mod (n 0) hζ, pow_eq_pow_mod (p * n 1) hζ, hmod']
    simp [key]
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
