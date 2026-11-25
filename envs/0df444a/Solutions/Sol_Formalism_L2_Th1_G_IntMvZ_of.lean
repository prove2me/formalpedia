-- Prove2me | solution 1 for Formalism.L2.Th1.G.IntMvZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:51.825843+00:00
-- url     : https://prove2.me/submissions/566c06d7-7b9a-404e-aec3-97ad0bceae9e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_L2_Th1_G_jets_of_dist_jets_holds
import Theorems.Thm_Formalism_L2_Th1_G_integral_dist_jets_holds
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hsX
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst
import Theorems.Thm_Formalism_LT_TorsProof_one_mem


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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
open HurwitzJetIntegrality
namespace Formalism.L2.Th1.G
theorem _root_.solution (h1 : JetsSubst) (h2 : IntJets) (h3 : JetsSubstOne) (h4 : JetsRing) : IntMvZ := by
  intro K _ _ R l linv hl hu n _ G hG
  classical
  have hX : Formalism.L2.Th1.C.IntPS R (PowerSeries.X : PowerSeries K) := by
    intro m
    rw [PowerSeries.coeff_X]
    split_ifs
    exacts [R.one_mem, R.zero_mem]
  have hsl : PowerSeries.HasSubst linv := by
    first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero hl.2.2.1
      | exact PowerSeries.HasSubst.of_constantCoeff_zero' hl.2.2.1
      | exact PowerSeries.HasSubst.of_constantCoeff_zero (by simpa using hl.2.2.1)
  have hlinv : JetsIn1 R linv := by
    have h := (jets_of_dist_jets_holds K R l linv PowerSeries.X hl).mp (integral_dist_jets_holds K R l PowerSeries.X hu hX)
    rwa [PowerSeries.subst_X hsl] at h
  have hXi : ∀ i : n, JetsIn R (MvPowerSeries.X i : MvPowerSeries n K) := by
    intro i κ
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · rw [mul_one]
      simpa using R.natCast_mem (mfact κ)
    · rw [mul_zero]
      exact R.zero_mem
  have hsX : ∀ i : n, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries n K) := by
    intro i
    first
      | exact PowerSeries.HasSubst.X i
      | exact PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
      | exact PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  refine h1 K R n n G _ (h2 K R n G hG) (fun i => ?_) (fun i => ?_)
  · rw [PowerSeries.constantCoeff_subst (hsX i)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl.2.2.1]
    · simp [zero_pow hd.ne']
  · exact h3 K R n linv (MvPowerSeries.X i) hlinv (MvPowerSeries.constantCoeff_X i) (hXi i)
end Formalism.L2.Th1.G
