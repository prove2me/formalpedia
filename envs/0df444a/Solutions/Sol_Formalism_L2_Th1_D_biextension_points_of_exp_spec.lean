-- Prove2me | solution 1 for Formalism.L2.Th1.D.biextension_points_of_exp_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:08.154956+00:00
-- url     : https://prove2.me/submissions/2d23efc0-9553-4f05-b20d-e04bd27750aa

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_simeq_sum
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_subst_sumE
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_simeq_sum
import Theorems.Thm_Formalism_L2_Th1_D_Pair_addC_log
import Theorems.Thm_Formalism_L2_Th1_D_ShiftIP_of_frobSq
import Theorems.Thm_Formalism_L2_Th1_D_frobenius_square
import Theorems.Thm_Formalism_L2_Th1_D_integral_part_lemma
import Theorems.Thm_Formalism_L2_Th1_D_letter_shift
import Theorems.Thm_Formalism_L2_Th1_D_subst_tilde
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Pair
open BiextensionSums
namespace Formalism.L2.Th1.D
theorem _root_.solution (hE : ExpSpec) (hM : MeanSimeqL) : BiextensionPointsIntegral := by
  intro K _ _ _ l d N0 N1 _ σ hU h2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hTr ζ hζ
  have hl : 2 ≤ l := hU.1.two_le
  have hLS := fun a b => (letter_shift K l d σ hU.1).2.2 N0 N1 a b
  have hSI := ShiftIP_of_frobSq frobenius_square K l d σ hU hd (Formalism.DworkPowerSeriesWeights.ZV d N0 N1)
  have hIP : ∀ x : Bool × ι × Fin N0 × Fin N1, IP l σ
      (if x.1 = false then
        linEL (d := d) σ (oms x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))
      else linOL (d := d) σ (om x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))) := by
    intro x
    split_ifs
    · exact (hSI _ (hLS x.2.2.1 x.2.2.2) (oms x.2.1) (hOw.1 x.2.1).2 (hOw.2 x.2.1).2).1
    · exact (hSI _ (hLS x.2.2.1 x.2.2.2) (om x.2.1) (hOw.1 x.2.1).1 (hOw.2 x.2.1).1).2
  choose Xt h0 hi hlog using fun x => integral_part_lemma K l σ hU _ _ (hIP x)
  refine ⟨Xt, fun x => ⟨h0 x, hi x⟩, hlog, ?_⟩
  have hsum : (∑ e : ι × Fin N0 × Fin N1, subst ![Xt (false, e), Xt (true, e)] be0) =
      ∑ ab : Fin N0 × Fin N1, ∑ r : ι, subst ![Xt (false, r, ab), Xt (true, r, ab)] be0 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [subst_sumE h0, hsum]
  refine simeq_sum (K := K) _ _ _ fun ab _ => ?_
  have key := hM K l d σ hU h2 hd F hF be0 hF1 hF2 ι om oms hOw hTr ζ hζ _
    (fun s => entLog (K := K) l (s, ab.1, ab.2)) (hLS ab.1 ab.2)
  rw [subst_tilde K l d σ hl be0 ι om oms _ _ (fun s => (hLS ab.1 ab.2 s).1)] at key
  have e : ∀ r : ι, subst ![Xt (false, r, ab), Xt (true, r, ab)] be0 =
      subst ![linEL (d := d) σ (oms r) (fun s => entLog (K := K) l (s, ab.1, ab.2)),
        linOL (d := d) σ (om r) (fun s => entLog (K := K) l (s, ab.1, ab.2))] (addC l be0) := by
    intro r
    rw [← addC_log hE hl (h0 _) (h0 _), hlog, hlog]
    simp
  simp only [e]
  exact key
end Formalism.L2.Th1.D
