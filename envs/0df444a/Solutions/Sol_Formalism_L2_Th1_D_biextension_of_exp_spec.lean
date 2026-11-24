-- Prove2me | solution 1 for Formalism.L2.Th1.D.biextension_of_exp_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:18.476494+00:00
-- url     : https://prove2.me/submissions/472df285-511b-46cf-8e9a-acdf3691bd71

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Theorems.Thm_P2M_Formalism_L2_Th1_D_BiextensionSums_map_lgF__08bf31594570
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_linSub_idM
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_map_sumE
import Theorems.Thm_P2M_Formalism_L2_Th1_D_BiextensionSums_subst_neg__523ff3cbd5a4
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_subst_map_linEL
import Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_subst_map_linOL
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_integral_map
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_entLog
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_simeqRules
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_mapSimeq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_simeqRules
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add
import Theorems.Thm_Formalism_L2_Th1_D_Pair_exp_log
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_subst1
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_sum
import Theorems.Thm_Formalism_L2_Th1_D_letter_shift
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_subst_mvExp__fa9db9cd36a6


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open BiextensionSums
namespace Formalism.L2.Th1.D
theorem _root_.solution (hE : ExpSpec) (hP : BiextensionPointsIntegral) : B0 := by
  intro K0 K _ _ _ _ _ _ l d N0 N1 _ σ j hU hj h2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hTr ζ hζ
    U0 Φ hU0 hΦ0 hΦ
  have hl : 2 ≤ l := hU.1.two_le
  obtain ⟨Xt, hX, hlog, hS⟩ := hP K0 l d N0 N1 σ hU h2 hd F hF be0 hF1 hF2 ι om oms hOw hTr ζ hζ
  have hR := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (ZV d N0 N1)
  have hs0 : HasSubst Xt := hasSubst_of_constantCoeff_zero fun x => (hX x).1
  obtain ⟨Xp, hXp⟩ : ∃ Xp : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries (ZV d N0 N1) K,
      ∀ x, Xp x = map j (Xt x) := ⟨fun x => map j (Xt x), fun _ => rfl⟩
  have hXp' : (fun x => map j (Xt x)) = Xp := funext fun x => (hXp x).symm
  have h0 : ∀ x, constantCoeff (Xp x) = 0 := fun x => by
    rw [hXp, constantCoeff_map, (hX x).1, map_zero]
  have hi : ∀ x, Integral (Xp x) := fun x => by
    rw [hXp]
    exact Formalism.DworkPowerSeriesWeights.Transfer.integral_map j hj (hX x).2
  have hs : HasSubst Xp := hasSubst_of_constantCoeff_zero h0
  have hE0 : ∀ (a : Fin N0) (b : Fin N1) (s : ZMod d),
      constantCoeff (entLog (K := K0) l (s, a, b)) = 0 :=
    fun a b s => ((letter_shift K0 l d σ hU.1).2.2 N0 N1 a b s).1
  have hE1 : ∀ (a : Fin N0) (b : Fin N1) (s : ZMod d),
      constantCoeff (entLog (K := K) l (s, a, b)) = 0 :=
    fun a b s => ((letter_shift K l d (RingHom.id K) hU.1).2.2 N0 N1 a b s).1
  obtain ⟨bm, hbm⟩ : ∃ bm, bm = map j (beMean (d := d) l σ be0 om oms ζ) := ⟨_, rfl⟩
  obtain ⟨Bt, hBt⟩ : ∃ Bt : MvPowerSeries (ZV d N0 N1) K, Bt = ∑ ab : Fin N0 × Fin N1,
      subst (fun s => entLog (K := K) l (s, ab.1, ab.2)) bm := ⟨_, rfl⟩
  have hmapB : map j (∑ ab : Fin N0 × Fin N1, subst
      (fun s => entLog (K := K0) l (s, ab.1, ab.2)) (beMean (d := d) l σ be0 om oms ζ)) = Bt := by
    rw [map_sum, hBt]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [map_subst (hasSubst_of_constantCoeff_zero fun s => hE0 ab.1 ab.2 s), hbm]
    simp only [Formalism.DworkPowerSeriesWeights.Transfer.map_entLog]
  have hS' : Simeq Bt (subst Xp (sumE (map j be0))) := by
    have := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq K0 K _ j hj).1 _ _ hS
    rwa [hmapB, map_subst hs0, map_sumE, hXp'] at this
  have hΦ' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Bool × ι × Fin N0 × Fin N1)).2.2.2.2 _ Φ _ Xp h0 hi hΦ
  have hBΦ : Simeq Bt (subst Xp Φ) := hR.2.2.1 _ _ _ hS' (hR.2.1 _ _ hΦ')
  have hsΦ0 : constantCoeff (subst Xp Φ) = 0 := constantCoeff_subst_eq_zero hs h0 hΦ0
  have hBt0 : constantCoeff Bt = 0 := by
    have := hBΦ.1
    rwa [map_sub, hsΦ0, sub_zero] at this
  have hnB0 : constantCoeff (-Bt) = 0 := by rw [map_neg, hBt0, neg_zero]
  refine ⟨mvExp (Bt - subst Xp Φ) * subst Xp U0,
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hBΦ.2 (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' h0 hi hU0), ?_⟩
  intro g hg0 hgE
  have hg : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hx : ∀ x, subst g (Xp x) = xOfZ l j σ om oms x := by
    intro x
    have ha : constantCoeff (subst g (Xp x)) = 0 := constantCoeff_subst_eq_zero hg hg0 (h0 x)
    have hlg : PowerSeries.subst (subst g (Xp x)) (lgF K l) =
        subst g (map j (PowerSeries.subst (Xt x) (lgF K0 l))) := by
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX x).1), map_lgF',
        ← hXp, subst_subst1 hg (PowerSeries.HasSubst.of_constantCoeff_zero (h0 x))]
    rw [← exp_log hE hl ha, hlg, hlog]
    unfold xOfZ
    congr 1
    split_ifs
    · exact subst_map_linEL l j σ _ _ _ hg hgE
    · exact subst_map_linOL l j σ _ _ _ hg hgE
  have hmain : subst Xp (mvExp (-Φ) * U0) =
      mvExp (-Bt) * (mvExp (Bt - subst Xp Φ) * subst Xp U0) := by
    rw [subst_mul hs, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hs (by rw [map_neg, hΦ0, neg_zero]),
      ← mul_assoc, ← mvExp_add hnB0 hBΦ.1, subst_neg' hs]
    congr 2
    ring
  have hgB : subst g Bt = bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) bm := by
    unfold bSum
    rw [linSub_idM, hBt, subst_sum hg]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun s => hE1 ab.1 ab.2 s) hg]
    simp only [hgE]
  have hxf : xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms = fun x => subst g (Xp x) :=
    funext fun x => (hx x).symm
  unfold thetaInZ thetaZ
  rw [linSub_idM, subst_self, id, ← hbm, ← hgB, hxf, ← subst_comp_subst_apply hs hg, hmain,
    subst_mul hg, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hg hnB0, subst_neg' hg, neg_smul, one_smul, mul_comm]
end Formalism.L2.Th1.D
