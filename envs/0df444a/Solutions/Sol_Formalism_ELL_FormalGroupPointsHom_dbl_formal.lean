-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.dbl_formal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:56.879832+00:00
-- url     : https://prove2.me/submissions/5761e7c1-6df6-428a-8702-d83993cf2673

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_subst_XX
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_cc_subst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_fg_ne_zero
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_x_X0_ne_formal_group
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_x_X0_ne_x_X1
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_chord_add
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_exists_unit_factor
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_xOf_ne_of_hom
import Theorems.Thm_Formalism_ELL_wSeriesNonsingularPoint_holds
import Theorems.Thm_P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678


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
variable {K : Type u} [Field K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) (F : FormalGroup K)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries)
    (hy : yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠
      (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))) :
    F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] ≠ 0 ∧
    xOf w (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0]) =
      (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.addX
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        ((3 * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ^ 2
          + 2 * (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂
            * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
          + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₄
          - (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁
            * (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))) /
          (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) -
            (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
              (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
              (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)))) ∧
    yOf w (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0]) =
      (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.addY
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        ((3 * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ^ 2
          + 2 * (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂
            * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
          + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₄
          - (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁
            * (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))) /
          (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) -
            (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
              (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
              (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)))) := by
  classical
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set z1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hz1
  set G := F.toPowerSeries with hG
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have c1 : MvPowerSeries.constantCoeff z1 = 0 := by simp [hz1]
  have n0 : z0 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 0
  have n1 : z1 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 1
  have cG : MvPowerSeries.constantCoeff G = 0 := F.zero_constantCoeff
  have nG : G ≠ 0 := fg_ne_zero F
  set D := G.subst ![z0, z0] with hD
  have cD : MvPowerSeries.constantCoeff D = 0 := cc_subst2 cG c0 c0
  have p0 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z0 c0 n0
  have p1 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z1 c1 n1
  obtain ⟨pG, eG⟩ := WeierstrassCoordinateSubstitution.chord_add z0 z1 G p0 p1 (x_X0_ne_x_X1 hw) hch
  have x0G := x_X0_ne_formal_group hw F
  have chH := hS K W w hw G cG hch (Fin 2) z0 G c0 cG n0 nG x0G
  obtain ⟨pH, eH⟩ := WeierstrassCoordinateSubstitution.chord_add z0 G _ p0 pG x0G chH
  have h0s : PowerSeries.HasSubst z0 := PowerSeries.HasSubst.of_constantCoeff_zero c0
  have h1s : PowerSeries.HasSubst z1 := PowerSeries.HasSubst.of_constantCoeff_zero c1
  have hassoc : G.subst ![D, z1] = G.subst ![z0, G] := by
    have := F.assoc' h0s h0s h1s
    rw [← hG] at this
    rw [hD, this, hz0, hz1, subst_XX]
  by_cases hD0 : D = 0
  · exfalso
    have hHz : G.subst ![z0, G] = z1 := by
      rw [← hassoc, hD0]; exact F.zero_add h1s
    have e1 : WeierstrassCurve.Affine.Point.some _ _ pH =
        WeierstrassCurve.Affine.Point.some _ _ p1 := by
      rw [WeierstrassCurve.Affine.Point.some.injEq, hHz]; exact ⟨rfl, rfl⟩
    rw [e1, ← eG] at eH
    have h2 : WeierstrassCurve.Affine.Point.some _ _ p0 + WeierstrassCurve.Affine.Point.some _ _ p0 = 0 := by
      calc _ = (WeierstrassCurve.Affine.Point.some _ _ p0 + (WeierstrassCurve.Affine.Point.some _ _ p0 +
              WeierstrassCurve.Affine.Point.some _ _ p1)) - WeierstrassCurve.Affine.Point.some _ _ p1 := by
            abel
        _ = 0 := by rw [eH, sub_self]
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at h3
    exact hy h3.2
  · refine ⟨hD0, ?_⟩
    have hφ : MvPowerSeries.HasSubst ![(0 : MvPowerSeries (Fin 2) K), z1] := hasSubst2 (by simp) c1
    have xD1 : xOf w D ≠ xOf w z1 := by
      refine WeierstrassCoordinateSubstitution.xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom hφ) D z1 cD c1 hD0 n1 ?_ ?_
      · rw [MvPowerSeries.coe_substAlgHom, hD, MvPowerSeries.subst_comp_subst_apply
          (hasSubst2 c0 c0) hφ]
        have e2 : (fun i => MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) K), z1] (![z0, z0] i)) =
            (0 : Fin 2 → MvPowerSeries (Fin 2) K) := by
          funext i; fin_cases i <;> simp [hz0, MvPowerSeries.subst_X hφ]
        rw [e2]
        exact MvPowerSeries.subst_zero_of_constantCoeff_zero cG
      · rw [MvPowerSeries.coe_substAlgHom, hz1, MvPowerSeries.subst_X hφ]; simpa using n1
    have pD := wSeriesNonsingularPoint_holds K W w hw (Fin 2) D cD hD0
    have chD := hS K W w hw G cG hch (Fin 2) D z1 cD c1 hD0 n1 xD1
    obtain ⟨pK, eK⟩ := WeierstrassCoordinateSubstitution.chord_add D z1 _ pD p1 xD1 chD
    have e1 : WeierstrassCurve.Affine.Point.some _ _ pK =
        WeierstrassCurve.Affine.Point.some _ _ pH := by
      rw [WeierstrassCurve.Affine.Point.some.injEq, hassoc]; exact ⟨rfl, rfl⟩
    rw [e1, ← eH, ← eG] at eK
    have h2 : WeierstrassCurve.Affine.Point.some _ _ pD =
        WeierstrassCurve.Affine.Point.some _ _ p0 + WeierstrassCurve.Affine.Point.some _ _ p0 := by
      have := eK
      rw [← add_assoc] at this
      exact add_right_cancel this
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy,
      WeierstrassCurve.Affine.Point.some.injEq,
      WeierstrassCurve.Affine.slope_of_Y_ne rfl hy] at h2
    exact h2
end Formalism.ELL.FormalGroupPointsHom
