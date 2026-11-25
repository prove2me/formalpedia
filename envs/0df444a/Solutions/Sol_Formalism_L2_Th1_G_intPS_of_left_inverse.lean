-- Prove2me | solution 1 for Formalism.L2.Th1.G.intPS_of_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:39:52.664801+00:00
-- url     : https://prove2.me/submissions/55896952-898b-4767-9e78-2f8534bc0f78

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hs1
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_subst
import Theorems.Thm_Formalism_LT_InvIntP_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.G
theorem _root_.solution (R : Subring K) {f g : PowerSeries K} (hf : IntPS R f)
    (hf0 : PowerSeries.constantCoeff f = 0) (hu : (PowerSeries.coeff 1 f)⁻¹ ∈ R)
    (hne : PowerSeries.coeff 1 f ≠ 0) (hg : PowerSeries.subst f g = PowerSeries.X) : IntPS R g := by

  let f' : PowerSeries R := PowerSeries.mk fun n => ⟨PowerSeries.coeff n f, hf n⟩
  have hmap : PowerSeries.map R.subtype f' = f := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hf'0 : PowerSeries.constantCoeff f' = 0 := by
    apply Subtype.ext
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    simpa using hf0
  have hf'1 : IsUnit (PowerSeries.coeff 1 f') := by
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff 1 f)⁻¹, hu⟩ ?_
    apply Subtype.ext
    rw [PowerSeries.coeff_mk]
    exact mul_inv_cancel₀ hne
  set t' : PowerSeries R := f'.substInvOfIsUnit hf'1 with ht'
  have ht'0 : PowerSeries.constantCoeff t' = 0 := PowerSeries.constantCoeff_substInvOfIsUnit f' hf'1
  have hr : PowerSeries.subst t' f' = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right f' hf'0 hf'1
  set t : PowerSeries K := PowerSeries.map R.subtype t' with ht
  have ht0 : PowerSeries.constantCoeff t = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ht, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, ht'0, map_zero]
  have hft : PowerSeries.subst t f = PowerSeries.X := by
    have := PowerSeries.map_subst (PowerSeries.HasSubst.substInvOfIsUnit f' hf'1)
      (h := R.subtype) f'
    rw [← ht', hr, hmap] at this
    rw [← PowerSeries.map_X R.subtype]
    exact this.symm
  have hgt : g = t := by
    have key := Pts.subst_subst hf0 ht0 g
    rw [hg, hft, PowerSeries.subst_X (JetSubstitutionLemmas.hs1 ht0), PowerSeries.X_subst] at key
    exact key.symm
  intro n
  rw [hgt, ht, PowerSeries.coeff_map]
  exact (PowerSeries.coeff n t').2
end Formalism.L2.Th1.G
