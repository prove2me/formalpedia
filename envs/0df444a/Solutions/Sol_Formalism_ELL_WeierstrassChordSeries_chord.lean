-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.chord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:25.823803+00:00
-- url     : https://prove2.me/submissions/9afb0f90-c164-4a74-ae0c-897a851577b7

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_vieta
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_G_inv
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_map_lineCoeffCubic
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_map_lineCoeffQuadratic
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_map_lineCoeffLinear
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_map_lineCoeffConst
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_chord_field
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_mul
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_X
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_nu_ne
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_chordCoeffCubic
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_linearCoeff_thirdParam
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_dd_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_formalSum
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_wF_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_weq_iff
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_X_ne
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_ne_zero_of_L
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_v_ne_of_G

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
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (hU : WSubstUnique.{u}) (hw : WFixed W w) :
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) (F2 W w) := by
  haveI hdom : IsDomain (MvPowerSeries (Fin 2) K) := by
    first
      | infer_instance
      | exact NoZeroDivisors.to_isDomain _
  have hι : Function.Injective (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) := IsFractionRing.injective _ _
  have hCa : ∀ a : K, (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (MvPowerSeries.C a) = algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) a := fun a => by
    first
      | rfl
      | (rw [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))]; rfl)
      | simp [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))]
  have hE : ∀ s : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff s = 0 →
      G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄)
        (ca W.a₆) s (w.subst s) = 0 :=
    fun s hs => (weq_iff W s _).mp (hU K W w hw (Fin 2) s hs).1
  have hG0 := hE (MvPowerSeries.X 0) (by simp)
  have hG1 := hE (MvPowerSeries.X 1) (by simp)
  have hv0 : lam w * MvPowerSeries.X 0 + nu w = Wi w 0 := by
    rw [nu]
    ring
  have hv1 : lam w * MvPowerSeries.X 1 + nu w = Wi w 1 := by
    rw [nu]
    linear_combination lam_mul w
  have hc0 : MvPowerSeries.constantCoeff (C3 W w) ≠ 0 := by
    rw [constantCoeff_chordCoeffCubic hw]
    exact one_ne_zero
  have hcinv : C3 W w * (C3 W w)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ hc0
  have he1 : C3 W w * (MvPowerSeries.X 0 + MvPowerSeries.X 1 + Formalism.ELL.WeierstrassChordSeries.z3 W w)
      + C2 W w = 0 := by
    rw [Formalism.ELL.WeierstrassChordSeries.z3]
    linear_combination (-C2 W w) * hcinv
  obtain ⟨hG3, he2, he3⟩ := vieta (a1 := ca W.a₁) (a2 := ca W.a₂)
    (a3 := ca W.a₃) (a4 := ca W.a₄) (a6 := ca W.a₆) (l := lam w)
    (n := nu w) (z1 := MvPowerSeries.X 0) (z2 := MvPowerSeries.X 1) (z3 := Formalism.ELL.WeierstrassChordSeries.z3 W w)
    X_ne (by rw [hv0]; exact hG0) (by rw [hv1]; exact hG1) he1
  have hD0' : MvPowerSeries.constantCoeff (dd W w) ≠ 0 := by
    rw [dd_cc hw]
    norm_num
  have hDinv : (dd W w)⁻¹ * dd W w = 1 := MvPowerSeries.inv_mul_cancel _ hD0'
  have hD0 : dd W w ≠ 0 := fun h => hD0' (by rw [h, map_zero])
  have hfD : F2 W w * dd W w = Formalism.ELL.WeierstrassChordSeries.z3 W w := by
    rw [F2, mul_assoc, hDinv, mul_one]
  have huD : wF W w * dd W w = w3 W w := by
    rw [wF, mul_assoc, hDinv, mul_one]
  have hinv := G_inv (a1 := ca W.a₁) (a2 := ca W.a₂)
    (a3 := ca W.a₃) (a4 := ca W.a₄) (a6 := ca W.a₆)
    (z := Formalism.ELL.WeierstrassChordSeries.z3 W w) (v := w3 W w) (d := dd W w) hfD huD rfl hD0 hG3
  have hsub : wF W w = w.subst (F2 W w) :=
    (hU K W w hw (Fin 2) (F2 W w) (constantCoeff_formalSum hw)).2 _
      (wF_cc hw) ((weq_iff W _ _).mpr hinv)
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 :=
    ne_zero_of_L (i := 0) (by rw [L_X]; simp)
  have hX1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ≠ 0 :=
    ne_zero_of_L (i := 1) (by rw [L_X]; simp)
  have hz3 : Formalism.ELL.WeierstrassChordSeries.z3 W w ≠ 0 :=
    ne_zero_of_L (i := 0) (by rw [linearCoeff_thirdParam hw]; norm_num)
  have hw0 : Wi w 0 ≠ 0 := v_ne_of_G W hX0 hG0
  have hw1 : Wi w 1 ≠ 0 := v_ne_of_G W hX1 hG1
  have hv3 : w3 W w ≠ 0 := v_ne_of_G W hz3 hG3
  have hc : C3 W w ≠ 0 := fun h => hc0 (by rw [h, map_zero])
  have key := chord_field (F := (FractionRing (MvPowerSeries (Fin 2) K))) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₁) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₂)
    (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₃) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₄) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₆)
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (MvPowerSeries.X 0)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (MvPowerSeries.X 1)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (Formalism.ELL.WeierstrassChordSeries.z3 W w))
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (Wi w 0)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (Wi w 1)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (w3 W w))
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (lam w)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (nu w)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (F2 W w)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (wF W w))
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (dd W w))
    (by rw [← hv0, map_add, map_mul]) (by rw [← hv1, map_add, map_mul]) (by rw [w3, map_add, map_mul])
    (by
      have := congrArg (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) he1
      simpa [C3, C2, map_lineCoeffCubic, map_lineCoeffQuadratic, hCa,
        ca] using this)
    (by
      have := congrArg (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) he2
      simpa [map_lineCoeffCubic, map_lineCoeffLinear, hCa, ca] using this)
    (by
      have := congrArg (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) he3
      simpa [map_lineCoeffCubic, map_lineCoeffConst, hCa, ca] using this)
    (by
      have := (map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hc
      simpa [C3, map_lineCoeffCubic, hCa, ca] using this)
    ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hw0) ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hw1)
    ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hv3) ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr (nu_ne hw))
    (hι.ne X_ne)
    (by
      rw [dd]
      simp [hCa, ca])
    ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hD0)
    (by rw [← map_mul, hfD]) (by rw [← map_mul, huD])
  obtain ⟨hx, hy⟩ := key
  unfold Formalism.ELL.ChordAt Formalism.ELL.xOf Formalism.ELL.yOf
  rw [← hsub]
  first
    | exact ⟨hx, hy⟩
    | (refine ⟨?_, ?_⟩
       · convert hx using 1
       · convert hy using 1
         simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
           WeierstrassCurve.Affine.negAddY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
         rfl)
end Formalism.ELL.WeierstrassChordSeries
