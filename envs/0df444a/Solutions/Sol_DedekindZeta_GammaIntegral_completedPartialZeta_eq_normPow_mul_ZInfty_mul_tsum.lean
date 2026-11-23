-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:54:56.243633+00:00
-- url     : https://prove2.me/submissions/56480d22-2697-4d38-9d64-ab2de34e5e4f

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_absdisc_rpow_mul_I_eq_ZInfty
import Theorems.Thm_DedekindZeta_GammaIntegral_cone_integral_idealThetaKernel_eq

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped nonZeroDivisors
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    DedekindZeta.completedPartialZeta K a s
      = (Ideal.absNorm a : ℂ) ^ s * DedekindZeta.ZInfty K s *
          ∑' I : {I : (Ideal (RingOfIntegers K))⁰ //
                    (a ∣ (I : Ideal (RingOfIntegers K))) ∧
                      Submodule.IsPrincipal (I : Ideal (RingOfIntegers K))},
              (Ideal.absNorm (I : Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Units.torsionOrder_ne_zero K)
  have hpos : (0 : ℝ) < s.re := by linarith
  rw [DedekindZeta.completedPartialZeta, cone_integral_idealThetaKernel_eq s hs ha,
    ← absdisc_rpow_mul_I_eq_ZInfty K hpos]
  field_simp
end DedekindZeta.GammaIntegral
