-- Prove2me | solution 1 for Formalism.L2.Th1.C.subst_binomSeries_eq_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:00.868498+00:00
-- url     : https://prove2.me/submissions/b9af5c6a-bd63-4726-b433-2e8c194f84b7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffSubstBinomSeries
import Theorems.Thm_Formalism_L2_Th1_C_binomSeries_ode
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_subst_binomSeries
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_subst
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_hasSubst_of_cc
import Theorems.Thm_Formalism_L2_Th1_C_isUnit_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_neg
import Theorems.Thm_Formalism_L2_Th1_C_pderiv_mvExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C
theorem _root_.solution (z : K) {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (mvExp f - 1) (binomSeries z) = mvExp (z • f) := by
  have hg : MvPowerSeries.constantCoeff (mvExp f - 1) = 0 := by
    rw [map_sub, constantCoeff_mvExp hf, map_one, sub_self]
  have hs : PowerSeries.HasSubst (mvExp f - 1) := hasSubst_of_cc hg
  have hzf : MvPowerSeries.constantCoeff (z • f) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]
  have hnzf : MvPowerSeries.constantCoeff (-(z • f)) = 0 := by rw [map_neg, hzf, neg_zero]
  set B := PowerSeries.subst (mvExp f - 1) (binomSeries z) with hB
  have hode : mvExp f * PowerSeries.subst (mvExp f - 1) (PowerSeries.derivative K (binomSeries z))
      = z • B := by
    have h := congrArg (PowerSeries.subst (mvExp f - 1)) (binomSeries_ode z)
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_add hs, PowerSeries.subst_X hs,
      PowerSeries.subst_smul hs, ← PowerSeries.coe_substAlgHom hs, map_one,
      PowerSeries.coe_substAlgHom hs] at h
    rw [hB, ← h]
    ring
  have hd : ∀ i, MvPowerSeries.pderiv K i B =
      MvPowerSeries.C z * MvPowerSeries.pderiv K i f * B := by
    intro i
    apply (isUnit_mvExp hf).mul_left_cancel
    rw [hB, IntegralMvPolynomialLemmas.pderiv_subst _ hg, ← mul_assoc, hode, map_sub, MvPowerSeries.pderiv_one, sub_zero,
      pderiv_mvExp hf, MvPowerSeries.smul_eq_C_mul]
    ring
  have key : B * mvExp (-(z • f)) = 1 := by
    refine MvPowerSeries.pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, pderiv_mvExp hnzf, hd, map_neg, MvPowerSeries.smul_eq_C_mul,
        Derivation.leibniz, MvPowerSeries.pderiv_C, MvPowerSeries.pderiv_one]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, constantCoeff_mvExp hnzf, hB, constantCoeff_subst_binomSeries z hg, map_one,
        mul_one]
  calc B = B * (mvExp (-(z • f)) * mvExp (z • f)) := by rw [mvExp_neg hzf, mul_one]
    _ = mvExp (z • f) := by rw [← mul_assoc, key, one_mul]
end Formalism.L2.Th1.C
