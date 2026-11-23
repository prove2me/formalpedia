-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.formalSum_mem_integralSeries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:51.625322+00:00
-- url     : https://prove2.me/submissions/90fc5b72-0835-4000-84ed-8cbe62358e76

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lineCoeffCubic_mem
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lineCoeffQuadratic_mem
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_chordCoeffCubic
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_dd_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_inv_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_X_mem_T
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constSeries_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_slope_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_intercept_mem_integralSeries

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
theorem _root_.solution (hw : WFixed W w) : F2 W w ∈ T W := by
  have h1 : ca W.a₁ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h2 : ca W.a₂ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h3 : ca W.a₃ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h4 : ca W.a₄ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h6 : ca W.a₆ ∈ T W := constSeries_mem_integralSeries (by simp)
  have hl := slope_mem_integralSeries hw
  have hn := intercept_mem_integralSeries hw
  have hC3 : C3 W w ∈ T W := lineCoeffCubic_mem _ h2 h4 h6 hl
  have hC2 : C2 W w ∈ T W := lineCoeffQuadratic_mem _ h1 h2 h3 h4 h6 hl hn
  have hC3i : (C3 W w)⁻¹ ∈ T W :=
    inv_mem_integralSeries hC3 (by rw [constantCoeff_chordCoeffCubic hw]; exact one_ne_zero) (by rw [constantCoeff_chordCoeffCubic hw, inv_one]; exact Subalgebra.one_mem _)
  have hz3 : z3 W w ∈ T W :=
    (T W).sub_mem ((T W).sub_mem ((T W).neg_mem (X_mem_T 0)) (X_mem_T 1)) ((T W).mul_mem hC2 hC3i)
  have hw3 : w3 W w ∈ T W := (T W).add_mem ((T W).mul_mem hl hz3) hn
  have hdd : dd W w ∈ T W :=
    (T W).add_mem ((T W).add_mem ((T W).neg_mem (T W).one_mem) ((T W).mul_mem h1 hz3))
      ((T W).mul_mem h3 hw3)
  have hddi : (dd W w)⁻¹ ∈ T W :=
    inv_mem_integralSeries hdd (by rw [dd_cc hw]; exact neg_ne_zero.mpr one_ne_zero)
      (by rw [dd_cc hw, inv_neg, inv_one]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))
  exact (T W).mul_mem hz3 hddi
end Formalism.ELL.WeierstrassChordSeries
