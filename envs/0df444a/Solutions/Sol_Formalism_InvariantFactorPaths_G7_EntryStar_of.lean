-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EntryStar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:15.802616+00:00
-- url     : https://prove2.me/submissions/6c25bef6-c0e8-466d-874c-4f9c5300012d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_lowOp_int
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_lowOp_deg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_lowOp_hom
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_zSub_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_aeval_entry
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_cc_zSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_cc_hhS
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_int_zSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_star_norm
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hT : TermBound) (hH : HhDecomp) (hC : ClassSubst)
    (hJ : Formalism.DworkPowerSeriesWeights.JetPairLin.{0}) (hS : StarArith) (hD : HasseDegree) (hM : MinorProdDegree) :
    EntryStar := by
  intro K _ _ p ν r0 r1 C _ u F TT ξ e l sf T I hyp
  obtain ⟨hp, hp2, hnp, hu, hF, hξ, hTn, he⟩ := hyp
  have hD0 : ∀ D : ℕ, D < p ^ (2 * (D + 1)) := fun D =>
    (Nat.lt_pow_self hp.one_lt).trans_le (Nat.pow_le_pow_right hp.pos (by omega))
  obtain ⟨Z, Y, hZ, hY, hZlow, hdec⟩ := hH K p ν r0 r1
    ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s + 1)
    ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s) u TT ξ hp hp2 hnp hu hξ (hD0 _)
  have hcc : MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p u) = 0 :=
    StarEntryOperators.cc_hhS hp.ne_zero u
  have hcls := hC K (ZV ν r0 r1) (TpV ν r1 ⊕ ZV ν r0 r1) (p : K) (hhS p u) F (zSub TT ξ) hcc
    (StarEntryOperators.cc_zSub TT ξ) (StarEntryOperators.int_zSub TT ξ hξ) hF
  have hcc' : MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (zSub TT ξ) (hhS (r0 := r0) (r1 := r1) p u)) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (StarEntryOperators.cc_zSub TT ξ))
      (StarEntryOperators.cc_zSub TT ξ) hcc
  have hjet : jetPair (topMonoP (Finsupp.equivFunOnFinite.symm e) * lowPoly (lowOp l sf T I))
      (MvPowerSeries.subst (zSub TT ξ) F) = jetPair (entryOp ξ e l sf T I) F := by
    have hz : (zSub TT ξ : ZV ν r0 r1 → _) = fun x =>
        ∑ i, MvPowerSeries.C (StarEntryOperators.Amat TT ξ i x) * MvPowerSeries.X i :=
      funext fun x => StarEntryOperators.zSub_eq TT ξ x
    rw [hz, hJ K (TpV ν r1 ⊕ ZV ν r0 r1) (ZV ν r0 r1) (StarEntryOperators.Amat TT ξ),
      StarEntryOperators.aeval_entry TT ξ e he]
  have one_pow_le : ∀ (a : K) (m : ℕ), ‖a‖ ≤ 1 → ‖a ^ m‖ ≤ 1 := fun a m ha => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have hsgn : ∀ m : ℕ, ‖(-1 : K) ^ m‖ ≤ 1 := fun m => one_pow_le _ _ (by simp)
  have hTB := hT K (TpV ν r1) (ZV ν r0 r1)
    (PhiI ν r0 r1 ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s + 1))
    (KapI ν r1 ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s + 1)) p
    ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s) (∑ s, lsN l sf s)
    (MvPowerSeries.subst (zSub TT ξ) (hhS p u)) (MvPowerSeries.subst (zSub TT ξ) F) Z Y
    (aAof p u TT ξ) (dAof p) (aBof u TT) (dBof p) (bBof p ξ) (Finsupp.equivFunOnFinite.symm e)
    (lowOp l sf T I) hp hnp hcc' hcls
    (by
      intro φ
      unfold aAof
      split_ifs
      · rw [norm_mul, norm_mul, norm_mul]
        exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (hu _) (norm_nonneg _) (hsgn _))
          (norm_nonneg _) (one_pow_le _ _ (hξ _ _))) (norm_nonneg _) (one_pow_le _ _ (hξ _ _))
      · simp)
    (by
      intro k
      unfold aBof
      split_ifs
      · rw [norm_mul]
        exact mul_le_one₀ (hu _) (norm_nonneg _) (hsgn _)
      · simp)
    (by
      intro k x
      unfold bBof colDir
      split_ifs
      · exact one_pow_le _ _ (hξ _ _)
      · simp)
    hZ hY hZlow hdec (StarEntryOperators.lowOp_int l sf T I hTn) (StarEntryOperators.lowOp_hom hM l sf T I) rfl
  rw [hjet] at hTB
  rcases hTB with h0 | ⟨α, β, i2, n, hn, hα, hβ, htop, hi2, hbound⟩
  · exact Or.inl h0
  right
  have hβT : ∀ k, β k ≠ 0 → k.1 ∈ TT := by
    intro k hk
    by_contra hkT
    exact hβ k hk (by unfold aBof; rw [if_neg hkT])
  obtain ⟨n0, hn0, hle, hdeg⟩ := hD K (ZV ν r0 r1) _ (bBof p ξ) β (lowOp l sf T I) n hn
  obtain ⟨hn0s, hn0d⟩ := StarEntryOperators.lowOp_deg hM l sf T I n0 hn0
  refine ⟨_, α, β, ?_, hβT, ?_, ?_, ?_⟩
  · intro φ hφ
    by_contra hφT
    exact hα φ hφ (by unfold aAof; rw [if_neg hφT])
  · intro τ
    have := htop τ
    rwa [Finsupp.equivFunOnFinite_symm_apply_apply] at this
  · intro h0
    rw [h0] at hn
    simp at hn
  · refine hbound.trans ?_
    have := StarEntryOperators.star_norm (K := K) hS hp hnp TT e (lsN l sf) he β hβT n (∑ φ, α φ) i2
      (fun s => (Finset.sum_le_sum fun x _ => hle (s, x)).trans (hn0s s).le)
      (by rw [hdeg, hn0d])
      (by
        intro k
        have h := htop (k.1, k.2.2)
        rw [Finsupp.equivFunOnFinite_symm_apply_apply] at h
        refine le_trans ?_ ((Nat.le_add_left _ _).trans h)
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum
          (f := fun k' => β k' * dBof p k' (k.1, k.2.2)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ k))
        simp only [dBof, Finsupp.single_eq_same]
        rw [mul_comm])
      hi2
    rw [Nat.cast_sum] at this
    exact this
end Formalism.InvariantFactorPaths.G7
