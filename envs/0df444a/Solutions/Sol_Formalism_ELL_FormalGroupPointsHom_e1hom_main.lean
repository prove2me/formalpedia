-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.e1hom_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:04.044942+00:00
-- url     : https://prove2.me/submissions/582e055e-89f0-40ca-ba7a-5fd36e7e7c05

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_eval_zero_left
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_eval_zero_right
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_case_chord
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_case_tan
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_case_inv
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_param_facts

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
theorem _root_.solution (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) (hPar : FormalGroupPointsParametrisation.{u})
    {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W) (hw : WFixed W w)
    (F : FormalGroup K) (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries)
    {inst : DecidableEq K} (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P) (hQ : InFormalGroupPoints Q) :
    uOf (P + Q) = evalMv2 F.toPowerSeries (uOf P) (uOf Q) := by
  rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
  · have := eval_zero_left F hFi (b := 0) (by simp)
    rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add]
    exact this.symm
  · obtain ⟨hb, -, -, -⟩ := param_facts hPar hW hw h2 hQ
    rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add]
    exact (eval_zero_left F hFi hb).symm
  · obtain ⟨ha, -, -, -⟩ := param_facts hPar hW hw h1 hP
    rw [← WeierstrassCurve.Affine.Point.zero_def, add_zero]
    exact (eval_zero_right F hFi ha).symm
  · obtain ⟨ha, hwa, hxa, hya⟩ := param_facts hPar hW hw h1 hP
    obtain ⟨hb, hwb, hxb, hyb⟩ := param_facts hPar hW hw h2 hQ
    change uOf (WeierstrassCurve.Affine.Point.some x1 y1 h1 +
      WeierstrassCurve.Affine.Point.some x2 y2 h2) = evalMv2 F.toPowerSeries (-x1 / y1) (-x2 / y2)
    generalize hA : -x1 / y1 = a at ha hwa hxa hya ⊢
    generalize hB : -x2 / y2 = b at hb hwb hxb hyb ⊢
    by_cases hx : x1 = x2
    · by_cases hy : y1 = W.toAffine.negY x2 y2
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy, ← hB]
        subst hx
        have hy2 : y2 = W.toAffine.negY x1 y1 := by
          rw [hy, WeierstrassCurve.Affine.negY_negY]
        subst hy2
        change (0 : K) = _
        rw [hxa, hya]
        exact (case_inv hU hS hW hw F hFi hch ha hwa).symm
      · have hyy := WeierstrassCurve.Affine.Y_eq_of_Y_ne h1.1 h2.1 hx hy
        subst hx
        subst hyy
        have hab : b = a := by rw [← hA, ← hB]
        subst hab
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
        change -(W.toAffine.addX x1 x1 (W.toAffine.slope x1 x1 y1 y1)) /
          W.toAffine.addY x1 x1 y1 (W.toAffine.slope x1 x1 y1 y1) = _
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
        have hM : -2 + W.a₁ * b + W.a₃ * evalPS w b ≠ 0 := by
          intro hM0
          apply hy
          rw [hxa, hya, WeierstrassCurve.Affine.negY]
          field_simp
          first | linear_combination hM0 | linear_combination -hM0
        rw [hxa, hya]
        exact case_tan hU hS hW hw F hFi hch ha hwa hM
    · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
      change -(W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2)) /
        W.toAffine.addY x1 x2 y1 (W.toAffine.slope x1 x2 y1 y2) = _
      rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
      have hN : a * evalPS w b - b * evalPS w a ≠ 0 := by
        intro h0
        apply hx
        rw [hxa, hxb]
        field_simp
        first | linear_combination h0 | linear_combination -h0
      rw [hxa, hxb, hya, hyb]
      exact case_chord hU hW hw F hFi hch ha hb hwa hwb hN
end Formalism.ELL.FormalGroupPointsHom
