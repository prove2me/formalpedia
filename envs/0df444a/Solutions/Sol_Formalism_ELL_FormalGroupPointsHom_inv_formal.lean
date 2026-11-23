-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.inv_formal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:56.035361+00:00
-- url     : https://prove2.me/submissions/cc47630d-cf5c-4fb1-8b0c-f3237f9345c3

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_cc_subst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_cc_wsubst
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_fg_ne_zero
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_x_X0_ne_formal_group
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_x_X0_ne_x_X1
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_weq_C
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_weq_of_C
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_chord_add
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_eq_of_xy
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_exists_unit_factor
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_eq_inv_of_map
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_mvsubst_psubst
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_ne_zero_of_weq
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
    (ψ : MvPowerSeries (Fin 2) K)
    (hψ : (1 - MvPowerSeries.C W.a₁ * MvPowerSeries.X 0 - MvPowerSeries.C W.a₃ *
      w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) * ψ = 1) :
    F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      -MvPowerSeries.X 0 * ψ] = 0 := by
  classical
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set z1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hz1
  set G := F.toPowerSeries with hG
  set w0 := w.subst z0 with hw0
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have c1 : MvPowerSeries.constantCoeff z1 = 0 := by simp [hz1]
  have n0 : z0 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 0
  have n1 : z1 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 1
  have cw0 : MvPowerSeries.constantCoeff w0 = 0 := cc_wsubst hw c0
  have cG : MvPowerSeries.constantCoeff G = 0 := F.zero_constantCoeff
  have nG : G ≠ 0 := fg_ne_zero F
  set E := 1 - MvPowerSeries.C W.a₁ * z0 - MvPowerSeries.C W.a₃ * w0 with hE
  have nE : E ≠ 0 := left_ne_zero_of_mul_eq_one hψ
  have nψ : ψ ≠ 0 := right_ne_zero_of_mul_eq_one hψ
  set J := -z0 * ψ with hJ
  have cJ : MvPowerSeries.constantCoeff J = 0 := by simp [hJ, c0]
  have nJ : J ≠ 0 := by
    rw [hJ, neg_mul, neg_ne_zero]; exact mul_ne_zero n0 nψ
  have hW0 := weq_C (hU K W w hw (Fin 2) z0 c0).1
  have hwJ : w.subst J = -w0 * ψ := by
    obtain ⟨_, huniq⟩ := hU K W w hw (Fin 2) J cJ
    refine (huniq _ (by simp [cw0]) (weq_of_C ?_)).symm
    have key : E ^ 3 * ((-w0 * ψ) - (J ^ 3 + MvPowerSeries.C W.a₁ * (J * (-w0 * ψ))
        + MvPowerSeries.C W.a₂ * (J ^ 2 * (-w0 * ψ)) + MvPowerSeries.C W.a₃ * (-w0 * ψ) ^ 2
        + MvPowerSeries.C W.a₄ * (J * (-w0 * ψ) ^ 2) + MvPowerSeries.C W.a₆ * (-w0 * ψ) ^ 3)) = 0 := by
      rw [hJ]
      linear_combination ((z0 ^ 3 + MvPowerSeries.C W.a₂ * (z0 ^ 2 * w0)
          + MvPowerSeries.C W.a₄ * (z0 * w0 ^ 2) + MvPowerSeries.C W.a₆ * w0 ^ 3)
          * ((E * ψ) ^ 2 + E * ψ + 1)
        - (MvPowerSeries.C W.a₁ * (z0 * w0) + MvPowerSeries.C W.a₃ * w0 ^ 2) * E * (E * ψ + 1)
        - w0 * E ^ 2) * hψ - hW0 - (1 + E) * w0 * hE
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (pow_ne_zero 3 nE))
  set j := algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) with hj
  have hinj : Function.Injective j := IsFractionRing.injective _ _
  have jne : ∀ {x}, x ≠ 0 → j x ≠ 0 := fun hx h => hx (hinj (by rw [h, map_zero]))
  have nw0 : w0 ≠ 0 := WeierstrassSubstitution.ne_zero_of_weq (hU K W w hw (Fin 2) z0 c0).1 n0
  have hjC : ∀ a : K, algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) a =
      j (MvPowerSeries.C a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K), MvPowerSeries.algebraMap_apply]
    rfl
  have hjψ : j ψ = (j E)⁻¹ := WeierstrassSubstitution.eq_inv_of_map j hψ
  have hjE : j E = 1 - j (MvPowerSeries.C W.a₁) * j z0 - j (MvPowerSeries.C W.a₃) * j w0 := by
    rw [hE]; simp only [map_sub, map_one, map_mul]
  have hxJ : xOf w J = xOf w z0 := by
    unfold xOf
    rw [hwJ, hJ, map_mul, map_mul, map_neg, map_neg, neg_mul, neg_mul, neg_div_neg_eq,
      mul_div_mul_right _ _ (jne nψ)]
  have hyJ : yOf w J = (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
      (xOf w z0) (yOf w z0) := by
    unfold yOf xOf
    rw [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, hjC, hjC,
      hwJ, map_mul, map_neg, hjψ]
    have h1 := jne nw0
    have h2 := jne nE
    rw [hjE] at h2 ⊢
    simp only [← hj, ← hw0]
    field_simp

  have p0 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z0 c0 n0
  have p1 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z1 c1 n1
  have pJ := wSeriesNonsingularPoint_holds K W w hw (Fin 2) J cJ nJ
  have hPJ : WeierstrassCurve.Affine.Point.some _ _ pJ = -WeierstrassCurve.Affine.Point.some _ _ p0 := by
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hxJ, hyJ⟩
  obtain ⟨pG, eG⟩ := WeierstrassCoordinateSubstitution.chord_add z0 z1 G p0 p1 (x_X0_ne_x_X1 hw) hch
  have xGJ : xOf w G ≠ xOf w J := by rw [hxJ]; exact (x_X0_ne_formal_group hw F).symm
  have chGJ := hS K W w hw G cG hch (Fin 2) G J cG cJ nG nJ xGJ
  obtain ⟨pH, eH⟩ := WeierstrassCoordinateSubstitution.chord_add G J _ pG pJ xGJ chGJ
  have hH : WeierstrassCurve.Affine.Point.some _ _ pH = WeierstrassCurve.Affine.Point.some _ _ p1 := by
    rw [← eH, hPJ, ← eG]; abel
  obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj hH
  have hGJ := hasSubst2 cG cJ
  have hHz1 : G.subst ![G, J] = z1 :=
    WeierstrassCoordinateSubstitution.eq_of_xy hwu hu _ _ (cc_subst2 cG cG cJ) c1 hx hy

  have hφ : MvPowerSeries.HasSubst ![z0, (0 : MvPowerSeries (Fin 2) K)] := hasSubst2 c0 (by simp)
  have hφz0 : MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] z0 = z0 := by
    rw [hz0, MvPowerSeries.subst_X hφ]; rfl
  have hφw0 : MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] w0 = w0 := by
    rw [hw0, WeierstrassSubstitution.mvsubst_psubst w z0 c0 _ hφ, hφz0]
  have hφE : MvPowerSeries.substAlgHom hφ E = E := by
    rw [hE, map_sub, map_sub, map_one, map_mul, map_mul, MvPowerSeries.coe_substAlgHom, hφz0,
      hφw0]
    simp
  have hφψ : MvPowerSeries.substAlgHom hφ ψ = ψ := by
    have h := congrArg (MvPowerSeries.substAlgHom hφ) hψ
    rw [map_mul, map_one, hφE, ← hψ] at h
    exact mul_left_cancel₀ nE h
  have hφJ : MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] J = J := by
    rw [← MvPowerSeries.coe_substAlgHom hφ, hJ, map_mul, map_neg, hφψ,
      MvPowerSeries.coe_substAlgHom, hφz0]
  have e := congrArg (MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)]) hHz1
  rw [MvPowerSeries.subst_comp_subst_apply hGJ hφ, hz1, MvPowerSeries.subst_X hφ] at e
  have e2 : (fun i => MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] (![G, J] i)) =
      ![z0, J] := by
    funext i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero c0)
    · simpa using hφJ
  rw [e2] at e
  simpa using e
end Formalism.ELL.FormalGroupPointsHom
