-- Prove2me | solution 1 for Formalism.L2.Th1.D.MeanSimeqL_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:29:03.052679+00:00
-- url     : https://prove2.me/submissions/949d102d-7c63-4f53-a678-f6a38bbc872d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sim_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_lamModule
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_sum


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open InverseCommuting
namespace Formalism.L2.Th1.D
theorem _root_.solution : TilInvariantL → MeanSimeqL := by
  intro hTI K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hT ζ hζ τ _ L hL
  have hLs : HasSubst L := hasSubst_of_constantCoeff_zero fun s => (hL s).1
  have h1 : 1 < l ^ d := Nat.one_lt_pow (by omega) hU.1.one_lt
  have hN0 : l ^ d - 1 ≠ 0 := by omega
  have hNK : ((l ^ d - 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hdiv : ¬ l ∣ l ^ d - 1 := by
    intro h
    have h2 : l ∣ (l ^ d - 1) + 1 := by
      rw [show (l ^ d - 1) + 1 = l ^ d by omega]
      exact dvd_pow_self l (by omega)
    exact hU.1.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
  have hk : ∀ k : ℕ, Simeq (subst L (subst (torus l (ζ ^ k)) (beTil (d := d) l σ be0 om oms)) -
      subst L (beTil (d := d) l σ be0 om oms)) 0 := by
    intro k
    have h := hTI K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hOw hT (ζ ^ k)
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) τ L hL
    unfold Simeq at h ⊢
    rwa [sub_zero]
  have hsum := sim_sum (Finset.range (l ^ d - 1)) _ _ fun k _ => hk k
  rw [Finset.sum_const_zero] at hsum
  have hlam := Formalism.InvariantFactorPaths.G7.Top.lamModule K τ l σ hU.1 hU.2.2.1 hU.2.2.2.2 _ (l ^ d - 1) hdiv hsum
  have e0 : (C (((l ^ d - 1 : ℕ) : K)⁻¹) : MvPowerSeries τ K) *
      ((l ^ d - 1) • subst L (beTil (d := d) l σ be0 om oms)) =
      subst L (beTil (d := d) l σ be0 om oms) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (C : K →+* MvPowerSeries τ K), ← map_mul,
      inv_mul_cancel₀ hNK, map_one, one_mul]
  have e : subst L (beMean (d := d) l σ be0 om oms ζ) - subst L (beTil (d := d) l σ be0 om oms) =
      C (((l ^ d - 1 : ℕ) : K)⁻¹) * ∑ k ∈ Finset.range (l ^ d - 1),
        (subst L (subst (torus l (ζ ^ k)) (beTil (d := d) l σ be0 om oms)) -
          subst L (beTil (d := d) l σ be0 om oms)) - 0 := by
    unfold beMean
    rw [subst_mul hLs, subst_C, Pair.subst_sum hLs, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, mul_sub, sub_zero, e0]
  unfold Simeq
  rw [e]
  exact hlam
end Formalism.L2.Th1.D
