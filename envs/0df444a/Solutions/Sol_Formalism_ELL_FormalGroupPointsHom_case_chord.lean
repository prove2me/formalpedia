-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.case_chord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:31.812802+00:00
-- url     : https://prove2.me/submissions/54889541-f4cd-41d0-b82a-5cb8fb6c7614

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_C
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_X0
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_X1
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_subst_X0
import Theorems.Thm_P2M_Formalism_ELL_FormalGroupPointsHom_evalMv2_zero__d743f55ca61b
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_ne_zero_of_eval
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_sub
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_subst_X1
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_X
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_C
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_chord_iff
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_chordPX
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_chordPY
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_fg_ne_zero
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_chordPX
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_chordPY
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_weqP
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_w_integral
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_weierstrassPolynomial_eq_zero_of_equation
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_eq_zero_of_weqP
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hjC_lemma
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_mul
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
theorem _root_.solution (hU : WSubstUnique.{u}) {W : WeierstrassCurve K} {w : PowerSeries K}
    (hW : IntegralModel W) (hw : WFixed W w) (F : FormalGroup K) (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries) {a b : K}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hwa : evalPS w a ≠ 0) (hwb : evalPS w b ≠ 0)
    (hN : a * evalPS w b - b * evalPS w a ≠ 0) :
    -(W.toAffine.addX (a / evalPS w a) (b / evalPS w b)
        ((-1 / evalPS w a - -1 / evalPS w b) / (a / evalPS w a - b / evalPS w b))) /
      W.toAffine.addY (a / evalPS w a) (b / evalPS w b) (-1 / evalPS w a)
        ((-1 / evalPS w a - -1 / evalPS w b) / (a / evalPS w a - b / evalPS w b)) =
      evalMv2 F.toPowerSeries a b := by
  classical
  have hwI := w_integral hW hw
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set z1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hz1
  set G := F.toPowerSeries with hG
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have c1 : MvPowerSeries.constantCoeff z1 = 0 := by simp [hz1]
  have cG : MvPowerSeries.constantCoeff G = 0 := F.zero_constantCoeff
  have iz0 : IntegralMv z0 := integral_X 0
  have iz1 : IntegralMv z1 := integral_X 1
  have iw0 : IntegralMv (w.subst z0) := SubstitutionCoefficientCongruence.integral_subst hwI c0 iz0
  have iw1 : IntegralMv (w.subst z1) := SubstitutionCoefficientCongruence.integral_subst hwI c1 iz1
  have iwG : IntegralMv (w.subst G) := SubstitutionCoefficientCongruence.integral_subst hwI cG hFi
  have ez0 : evalMv2 z0 a b = a := evalMv2_X0 a b
  have ez1 : evalMv2 z1 a b = b := evalMv2_X1 a b
  have ew0 : evalMv2 (w.subst z0) a b = evalPS w a := evalMv2_subst_X0 w a b
  have ew1 : evalMv2 (w.subst z1) a b = evalPS w b := evalMv2_subst_X1 w a b
  have nw0 : w.subst z0 ≠ 0 := ne_zero_of_eval (a := a) (b := b) (by rw [ew0]; exact hwa)
  have nw1 : w.subst z1 ≠ 0 := ne_zero_of_eval (a := a) (b := b) (by rw [ew1]; exact hwb)
  have nN : z0 * w.subst z1 - z1 * w.subst z0 ≠ 0 := by
    refine ne_zero_of_eval (a := a) (b := b) ?_
    rw [evalMv2_sub (SubstitutionCoefficientCongruence.integral_mul iz0 iw1) (SubstitutionCoefficientCongruence.integral_mul iz1 iw0) ha hb,
      evalMv2_mul iz0 iw1 ha hb, evalMv2_mul iz1 iw0 ha hb, ez0, ez1, ew0, ew1]
    exact hN
  have nwG : w.subst G ≠ 0 := WeierstrassSubstitution.ne_zero_of_weq (hU K W w hw (Fin 2) G cG).1 (fg_ne_zero F)
  set j := algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) with hj
  have hinj : Function.Injective j := IsFractionRing.injective _ _
  have jne : ∀ {x}, x ≠ 0 → j x ≠ 0 := fun hx h => hx (hinj (by rw [h, map_zero]))
  have hjN : j z0 * j (w.subst z1) - j z1 * j (w.subst z0) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]; exact jne nN
  unfold ChordAt xOf yOf at hch
  obtain ⟨hX, hY⟩ := (chord_iff (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine
    (jne nw0) (jne nw1) hjN (jne nwG)).mp hch
  rw [show (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁ =
      j (MvPowerSeries.C W.a₁) from hjC_lemma _,
    show (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂ =
      j (MvPowerSeries.C W.a₂) from hjC_lemma _, ← map_chordPX] at hX
  rw [show (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁ =
      j (MvPowerSeries.C W.a₁) from hjC_lemma _,
    show (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₃ =
      j (MvPowerSeries.C W.a₃) from hjC_lemma _, ← map_chordPY] at hY
  have hX' := hinj (hX.trans (map_zero j).symm)
  have hY' := hinj (hY.trans (map_zero j).symm)
  have hWq := weierstrassPolynomial_eq_zero_of_equation (hU K W w hw (Fin 2) G cG).1
  have eX := evalMv2_chordPX (integral_C h1) (integral_C h2) iz0 iz1 iw0 iw1 hFi iwG ha hb
  have eY := evalMv2_chordPY (integral_C h1) (integral_C h3) iz0 iz1 iw0 iw1 hFi iwG ha hb
  have eW := evalMv2_weqP (integral_C h1) (integral_C h2) (integral_C h3) (integral_C h4)
    (integral_C h6) hFi iwG ha hb
  rw [hX', evalMv2_zero'] at eX
  rw [hY', evalMv2_zero'] at eY
  rw [hWq, evalMv2_zero'] at eW
  simp only [evalMv2_C, ez0, ez1, ew0, ew1] at eX eY eW
  set c := evalMv2 G a b with hc
  set v := evalMv2 (w.subst G) a b with hv
  have hv0 : v ≠ 0 := by
    intro hv0
    rw [hv0] at eW eY
    have hc0 := eq_zero_of_weqP eW.symm
    rw [hc0] at eY
    apply mul_ne_zero hN hwa
    simp only [chordPY] at eY
    linear_combination -eY
  have hK := (chord_iff W.toAffine hwa hwb hN hv0 (c := c)).mpr ⟨eX.symm, eY.symm⟩
  rw [← hK.1, ← hK.2]
  field_simp
end Formalism.ELL.FormalGroupPointsHom
