-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.case_tan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:06.648822+00:00
-- url     : https://prove2.me/submissions/b72ddeb2-6902-4abb-b26b-c677e06a0d28

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
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_ne_zero_of_eval
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_X
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_C
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_subst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_tan_iff
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_tanPX
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_tanPY
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_mP
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_cc_subst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_dbl_formal
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_tanPX
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_tanPY
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_weqP
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_mP
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_w_integral
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_weierstrassPolynomial_eq_zero_of_equation
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_eq_zero_of_weqP
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hjC_lemma
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_subst
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_ne_zero_of_weq


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
    (ha : ‖a‖ < 1) (hwa : evalPS w a ≠ 0) (hM : -2 + W.a₁ * a + W.a₃ * evalPS w a ≠ 0) :
    -(W.toAffine.addX (a / evalPS w a) (a / evalPS w a)
        ((3 * (a / evalPS w a) ^ 2 + 2 * W.toAffine.a₂ * (a / evalPS w a) + W.toAffine.a₄
          - W.toAffine.a₁ * (-1 / evalPS w a)) /
          (-1 / evalPS w a - W.toAffine.negY (a / evalPS w a) (-1 / evalPS w a)))) /
      W.toAffine.addY (a / evalPS w a) (a / evalPS w a) (-1 / evalPS w a)
        ((3 * (a / evalPS w a) ^ 2 + 2 * W.toAffine.a₂ * (a / evalPS w a) + W.toAffine.a₄
          - W.toAffine.a₁ * (-1 / evalPS w a)) /
          (-1 / evalPS w a - W.toAffine.negY (a / evalPS w a) (-1 / evalPS w a))) =
      evalMv2 F.toPowerSeries a a := by
  classical
  have hwI := w_integral hW hw
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set G := F.toPowerSeries with hG
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have cG : MvPowerSeries.constantCoeff G = 0 := F.zero_constantCoeff
  have iz0 : IntegralMv z0 := integral_X 0
  have iw0 : IntegralMv (w.subst z0) := SubstitutionCoefficientCongruence.integral_subst hwI c0 iz0
  set D := G.subst ![z0, z0] with hD
  have cD : MvPowerSeries.constantCoeff D = 0 := cc_subst2 cG c0 c0
  have iD : IntegralMv D := integral_subst2 hFi iz0 iz0 c0 c0
  have iwD : IntegralMv (w.subst D) := SubstitutionCoefficientCongruence.integral_subst hwI cD iD
  have ez0 : evalMv2 z0 a a = a := evalMv2_X0 a a
  have ew0 : evalMv2 (w.subst z0) a a = evalPS w a := evalMv2_subst_X0 w a a
  have eD : evalMv2 D a a = evalMv2 G a a := by
    rw [hD, evalMv2_subst hFi iz0 iz0 c0 c0 ha ha, ez0]
  have nw0 : w.subst z0 ≠ 0 := ne_zero_of_eval (a := a) (b := a) (by rw [ew0]; exact hwa)
  have nM : mP (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₃) z0 (w.subst z0) ≠ 0 := by
    refine ne_zero_of_eval (a := a) (b := a) ?_
    rw [evalMv2_mP (integral_C h1) (integral_C h3) iz0 iw0 ha ha, evalMv2_C, evalMv2_C, ez0, ew0]
    exact hM
  set j := algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) with hj
  have hinj : Function.Injective j := IsFractionRing.injective _ _
  have jne : ∀ {x}, x ≠ 0 → j x ≠ 0 := fun hx h => hx (hinj (by rw [h, map_zero]))
  have hA1 : (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁ =
      j (MvPowerSeries.C W.a₁) := hjC_lemma _
  have hA2 : (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂ =
      j (MvPowerSeries.C W.a₂) := hjC_lemma _
  have hA3 : (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₃ =
      j (MvPowerSeries.C W.a₃) := hjC_lemma _
  have hA4 : (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₄ =
      j (MvPowerSeries.C W.a₄) := hjC_lemma _
  have hMFr : -2 + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁ * j z0
      + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₃ * j (w.subst z0)
      ≠ 0 := by
    rw [hA1, hA3]
    have := jne nM
    rwa [map_mP] at this
  have hyF : yOf w z0 ≠ (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
      (xOf w z0) (yOf w z0) := by
    intro h
    apply hMFr
    unfold yOf xOf at h
    rw [WeierstrassCurve.Affine.negY] at h
    have hw0' := jne nw0
    simp only [← hj] at h
    field_simp at h
    first | linear_combination h | linear_combination -h
  obtain ⟨nD, hxD, hyD⟩ := dbl_formal hU hS hw F hch hyF
  have nwD : w.subst D ≠ 0 := WeierstrassSubstitution.ne_zero_of_weq (hU K W w hw (Fin 2) D cD).1 nD
  unfold xOf yOf at hxD hyD
  obtain ⟨hX, hY⟩ := (tan_iff (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine
    (jne nw0) hMFr (jne nwD)).mp ⟨hxD, hyD⟩
  rw [hA1, hA2, hA3, hA4, ← map_tanPX] at hX
  rw [hA1, hA2, hA3, hA4, ← map_tanPY] at hY
  have hX' := hinj (hX.trans (map_zero j).symm)
  have hY' := hinj (hY.trans (map_zero j).symm)
  have hWq := weierstrassPolynomial_eq_zero_of_equation (hU K W w hw (Fin 2) D cD).1
  have eX := evalMv2_tanPX (integral_C h1) (integral_C h2) (integral_C h3) (integral_C h4) iz0 iw0
    iD iwD ha ha
  have eY := evalMv2_tanPY (integral_C h1) (integral_C h2) (integral_C h3) (integral_C h4) iz0 iw0
    iD iwD ha ha
  have eW := evalMv2_weqP (integral_C h1) (integral_C h2) (integral_C h3) (integral_C h4)
    (integral_C h6) iD iwD ha ha
  rw [hX', evalMv2_zero'] at eX
  rw [hY', evalMv2_zero'] at eY
  rw [hWq, evalMv2_zero'] at eW
  simp only [evalMv2_C, ez0, ew0, eD] at eX eY eW
  set c := evalMv2 G a a with hc
  set v := evalMv2 (w.subst D) a a with hv
  have hv0 : v ≠ 0 := by
    intro hv0
    rw [hv0] at eW eY
    have hc0 := eq_zero_of_weqP eW.symm
    rw [hc0] at eY
    apply mul_ne_zero (pow_ne_zero 2 hwa) hM
    simp only [tanPY] at eY
    linear_combination -eY
  have hK := (tan_iff W.toAffine hwa hM hv0 (c := c)).mpr ⟨eX.symm, eY.symm⟩
  rw [← hK.1, ← hK.2]
  field_simp
end Formalism.ELL.FormalGroupPointsHom
