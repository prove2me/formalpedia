-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.chordCoeffCubic_inversionDenom_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:04.954806+00:00
-- url     : https://prove2.me/submissions/a29a45b8-b5fb-498c-ad24-bef8c3e62ab8

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_X_mem_T
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constSeries_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_chordCoeffCubic
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_dd_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_intercept_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_inv_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lineCoeffCubic_mem
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lineCoeffQuadratic_mem
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_slope_mem_integralSeries


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
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
variable {w : PowerSeries K}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution (hw : WFixed W w) : C3 W w * (C3 W w)⁻¹ = 1 ∧ dd W w * (dd W w)⁻¹ = 1 ∧
    (C3 W w)⁻¹ ∈ T W ∧ (dd W w)⁻¹ ∈ T W := by
  have hA0 := Formalism.ELL.WeierstrassChordSeries.constantCoeff_chordCoeffCubic hw
  have hD0 := Formalism.ELL.WeierstrassChordSeries.dd_cc hw
  have hAne : cc (Formalism.ELL.WeierstrassChordSeries.C3 W w) ≠ 0 := by rw [hA0]; exact one_ne_zero
  have hDne : cc (Formalism.ELL.WeierstrassChordSeries.dd W w) ≠ 0 := by rw [hD0]; exact neg_ne_zero.mpr one_ne_zero
  have c1 : Formalism.ELL.WeierstrassChordSeries.ca W.a₁ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have c2 : Formalism.ELL.WeierstrassChordSeries.ca W.a₂ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have c3 : Formalism.ELL.WeierstrassChordSeries.ca W.a₃ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have c4 : Formalism.ELL.WeierstrassChordSeries.ca W.a₄ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have c6 : Formalism.ELL.WeierstrassChordSeries.ca W.a₆ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have hl := Formalism.ELL.WeierstrassChordSeries.slope_mem_integralSeries hw
  have hn := Formalism.ELL.WeierstrassChordSeries.intercept_mem_integralSeries hw
  have hA : Formalism.ELL.WeierstrassChordSeries.C3 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.C3
    exact Formalism.ELL.WeierstrassChordSeries.lineCoeffCubic_mem _ c2 c4 c6 hl
  have hAi : (Formalism.ELL.WeierstrassChordSeries.C3 W w)⁻¹ ∈ Formalism.ELL.WeierstrassChordSeries.T W :=
    Formalism.ELL.WeierstrassChordSeries.inv_mem_integralSeries hA hAne (by rw [hA0, inv_one]; exact one_mem _)
  have hQ : Formalism.ELL.WeierstrassChordSeries.C2 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.C2
    exact Formalism.ELL.WeierstrassChordSeries.lineCoeffQuadratic_mem _ c1 c2 c3 c4 c6 hl hn
  have hz : Formalism.ELL.WeierstrassChordSeries.z3 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.z3
    exact sub_mem (sub_mem (neg_mem (Formalism.ELL.WeierstrassChordSeries.X_mem_T 0)) (Formalism.ELL.WeierstrassChordSeries.X_mem_T 1)) (mul_mem hQ hAi)
  have hv : Formalism.ELL.WeierstrassChordSeries.w3 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.w3
    exact add_mem (mul_mem hl hz) hn
  have hD : Formalism.ELL.WeierstrassChordSeries.dd W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.dd
    exact add_mem (add_mem (neg_mem (one_mem _)) (mul_mem c1 hz)) (mul_mem c3 hv)
  exact ⟨MvPowerSeries.mul_inv_cancel _ hAne, MvPowerSeries.mul_inv_cancel _ hDne, hAi,
    Formalism.ELL.WeierstrassChordSeries.inv_mem_integralSeries hD hDne (by rw [hD0, inv_neg, inv_one]; exact neg_mem (one_mem _))⟩
end Formalism.ELL.CubeThreeAlt
