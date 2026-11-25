-- Prove2me | solution 1 for Formalism.L2.Th1.C.Calc.lg_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:21:38.93588+00:00
-- url     : https://prove2.me/submissions/82273350-ce94-45c0-82ba-82370f91a5ed

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ArithmeticFrobeniusAction
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourFoldOrthogonalSum
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FinsuppZmodOneEqSingle
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_GL3MeanSquares_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
import Theorems.Thm_Formalism_G_LogP_hb0
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_neg

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
namespace Formalism.L2.Th1.C
namespace Calc
open Pts
section CongCalc
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {σ : Type}
private lemma intMv_of_mul_eq_one_lemma {a b : MvPowerSeries σ K} (hb : IntMv R b)
    (hb0 : MvPowerSeries.constantCoeff b = 1) (hab : a * b = 1) : IntMv R a := by
  let bR : MvPowerSeries σ R := fun n => ⟨MvPowerSeries.coeff n b, hb n⟩
  have hmap : MvPowerSeries.map R.subtype bR = b := by
    ext n
    rw [MvPowerSeries.coeff_map]
    try rfl
  have hu : IsUnit bR := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    have h1 : MvPowerSeries.constantCoeff bR = 1 := by
      apply Subtype.ext
      show MvPowerSeries.coeff 0 b = 1
      first
        | exact hb0
        | exact (MvPowerSeries.coeff_zero_eq_constantCoeff_apply b).trans hb0
    rw [h1]
    exact isUnit_one
  obtain ⟨u, hu⟩ := hu
  have hc : MvPowerSeries.map R.subtype (↑u⁻¹ : MvPowerSeries σ R) * b = 1 := by
    rw [← hmap, ← map_mul, ← hu, Units.inv_mul, map_one]
  have ha : a = MvPowerSeries.map R.subtype (↑u⁻¹ : MvPowerSeries σ R) := by
    calc a = a * (b * MvPowerSeries.map R.subtype (↑u⁻¹ : MvPowerSeries σ R)) := by
          rw [mul_comm b, hc, mul_one]
      _ = _ := by rw [← mul_assoc, hab, one_mul]
  intro n
  rw [ha, MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff n (↑u⁻¹ : MvPowerSeries σ R)).2
end CongCalc
end Calc
namespace Calc
open Pts Formalism.HermitianLattices.IntegralLatticeDensity
section Construct
variable {K : Type} [Field K] [CharZero K] {O : Type} [CommRing O] [StarRing O]
variable {R : Subring K} {l linv : PowerSeries K} {τ : O →+* K}
end Construct
end Calc
end Formalism.L2.Th1.C
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Calc
open Pts
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {σ : Type}
namespace Formalism.L2.Th1.C.Calc
theorem _root_.solution {f : MvPowerSeries σ K} (hf : LG R f) : LG R (-f) := by
  unfold LG at *
  refine ⟨by rw [map_neg, hf.1, neg_zero], ?_⟩
  exact intMv_of_mul_eq_one_lemma hf.2 (constantCoeff_mvExp hf.1) (mvExp_neg hf.1)
end Formalism.L2.Th1.C.Calc
