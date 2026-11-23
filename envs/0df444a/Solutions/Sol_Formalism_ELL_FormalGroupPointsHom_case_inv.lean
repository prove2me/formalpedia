-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.case_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:06.566666+00:00
-- url     : https://prove2.me/submissions/fe47a190-a700-4228-9097-aaa1a6e3538c

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_C
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_X0
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_subst_X0
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_subst
import Theorems.Thm_P2M_Formalism_ELL_FormalGroupPointsHom_evalMv2_zero__d743f55ca61b
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_sub
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_neg
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_X
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_C
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_exists_inv_integral
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_cc_wsubst
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_inv_formal
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_w_integral
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hW : IntegralModel W) (hw : WFixed W w) (F : FormalGroup K)
    (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries) {a : K}
    (ha : ‖a‖ < 1) (hwa : evalPS w a ≠ 0) :
    evalMv2 F.toPowerSeries a
      (-(a / evalPS w a) / W.toAffine.negY (a / evalPS w a) (-1 / evalPS w a)) = 0 := by
  have hwI := w_integral hW hw
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set G := F.toPowerSeries with hG
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have iz0 : IntegralMv z0 := integral_X 0
  have iw0 : IntegralMv (w.subst z0) := SubstitutionCoefficientCongruence.integral_subst hwI c0 iz0
  have cw0 : MvPowerSeries.constantCoeff (w.subst z0) = 0 := cc_wsubst hw c0
  have ez0 : evalMv2 z0 a a = a := evalMv2_X0 a a
  have ew0 : evalMv2 (w.subst z0) a a = evalPS w a := evalMv2_subst_X0 w a a
  set E := 1 - MvPowerSeries.C W.a₁ * z0 - MvPowerSeries.C W.a₃ * w.subst z0 with hE
  have iE : IntegralMv E :=
    (IL K).sub_mem ((IL K).sub_mem (IL K).one_mem ((IL K).mul_mem (integral_C h1) iz0))
      ((IL K).mul_mem (integral_C h3) iw0)
  have cE : MvPowerSeries.constantCoeff E = 1 := by simp [hE, c0, cw0]
  obtain ⟨ψ, iψ, hEψ⟩ := exists_inv_integral iE cE
  have h0 := inv_formal hU hS hw F hch ψ hEψ
  have iJ : IntegralMv (-z0 * ψ) := (IL K).mul_mem ((IL K).neg_mem iz0) iψ
  have cJ : MvPowerSeries.constantCoeff (-z0 * ψ) = 0 := by simp [c0]
  have e := evalMv2_subst hFi iz0 iJ c0 cJ ha ha
  rw [h0, evalMv2_zero', ez0] at e
  have eJ : evalMv2 (-z0 * ψ) a a = -a * evalMv2 ψ a a := by
    rw [evalMv2_mul ((IL K).neg_mem iz0) iψ ha ha, evalMv2_neg iz0 ha ha, ez0]
  have eE : evalMv2 E a a * evalMv2 ψ a a = 1 := by
    rw [← evalMv2_mul iE iψ ha ha, hEψ, evalMv2_one]
  have eE' : evalMv2 E a a = 1 - W.a₁ * a - W.a₃ * evalPS w a := by
    rw [hE, evalMv2_sub ((IL K).sub_mem (IL K).one_mem ((IL K).mul_mem (integral_C h1) iz0))
      ((IL K).mul_mem (integral_C h3) iw0) ha ha, evalMv2_sub (IL K).one_mem
      ((IL K).mul_mem (integral_C h1) iz0) ha ha, evalMv2_one,
      evalMv2_mul (integral_C h1) iz0 ha ha, evalMv2_mul (integral_C h3) iw0 ha ha, evalMv2_C,
      evalMv2_C, ez0, ew0]
  have hEa : 1 - W.a₁ * a - W.a₃ * evalPS w a ≠ 0 := by
    rw [← eE']; exact left_ne_zero_of_mul_eq_one eE
  have hψa : evalMv2 ψ a a = (1 - W.a₁ * a - W.a₃ * evalPS w a)⁻¹ := by
    rw [← eE']; exact eq_inv_of_mul_eq_one_right eE
  rw [eJ, hψa] at e
  rw [show -(a / evalPS w a) / W.toAffine.negY (a / evalPS w a) (-1 / evalPS w a) =
      -a * (1 - W.a₁ * a - W.a₃ * evalPS w a)⁻¹ from ?_]
  · exact e.symm
  · rw [WeierstrassCurve.Affine.negY]
    have : -(-1 / evalPS w a) - W.toAffine.a₁ * (a / evalPS w a) - W.toAffine.a₃ =
        (1 - W.a₁ * a - W.a₃ * evalPS w a) / evalPS w a := by
      field_simp
      try ring
    rw [this]
    field_simp
end Formalism.ELL.FormalGroupPointsHom
