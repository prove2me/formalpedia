-- Prove2me | solution 1 for Formalism.FG.KeyVAux.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:07.200429+00:00
-- url     : https://prove2.me/submissions/2abf038b-7bf4-4858-b6a6-ec6ff8623fd7

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Theorems.Thm_Formalism_FG_KeyVAux_norm_add_le_of
import Theorems.Thm_Formalism_FG_KeyVAux_norm_sub_le_of
import Theorems.Thm_Formalism_FG_KeyVAux_bd_prod_sub
import Theorems.Thm_Formalism_FG_KeyVAux_bd_subst_sub
import Theorems.Thm_Formalism_FG_KeyVAux_subst_expand
import Theorems.Thm_Formalism_FG_KeyVAux_expand_map_subst
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_integral_subst_vector
import Theorems.Thm_Formalism_LT_FrobCongr_valid
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_add_le_of
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_sigma_le_one
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_sub_le_of
import Theorems.Thm_Formalism_LT_PowCongr_valid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.KeyVAux
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.KeyVAux
theorem _root_.solution (hC : Formalism.FG.CoeffBoundV.{u, v, v}) : Formalism.FG.FunEqSubstV.{u, v, w} := by
  intro K _ _ _ p q hq σ hS ι _ M hM f hf0 hfT τ α hα0 hαI
  obtain ⟨hp, ⟨h, hh, hqh⟩, hp1, hσ⟩ := id hS
  have hp1' : ‖(p : K)‖ ≤ 1 := hp1.le
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hppos : 0 < ‖(p : K)‖ := norm_pos_iff.mpr hpne
  have hαS : MvPowerSeries.HasSubst α := MvPowerSeries.hasSubst_of_constantCoeff_zero hα0
  obtain ⟨αq, hαq⟩ : ∃ αq : ι → MvPowerSeries τ K, αq = fun i => α i ^ q := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ι → MvPowerSeries τ K,
      β = fun i => MvPowerSeries.expand q hq (MvPowerSeries.map σ (α i)) := ⟨_, rfl⟩
  have hαqS : MvPowerSeries.HasSubst αq := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    rw [hαq, map_pow, hα0, zero_pow hq]
  have hβS : MvPowerSeries.HasSubst β := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    rw [hβ, MvPowerSeries.constantCoeff_expand, MvPowerSeries.constantCoeff_map, hα0, map_zero]
  have hαqI : ∀ i, IntegralMv (αq i) := by
    intro i; rw [hαq]; exact Formalism.FG.IntegralSubstitution.integral_pow (hαI i) q
  have hdiv : ∀ i, DivByMv (p : K) (αq i - β i) := by
    intro i; rw [hαq, hβ]; exact Formalism.LT.FrobCongr_valid K p q hq σ hS τ (α i) (hαI i)
  have hβI : ∀ i, IntegralMv (β i) := by
    intro i d
    have e : MvPowerSeries.coeff d (β i)
        = MvPowerSeries.coeff d (αq i) - MvPowerSeries.coeff d (αq i - β i) := by
      rw [map_sub]; ring
    rw [e]
    exact norm_sub_le_of (hαqI i d) ((hdiv i d).trans hp1')

  have e3 : ∀ k, MvPowerSeries.expand q hq (MvPowerSeries.map σ (MvPowerSeries.subst α (f k))) =
      MvPowerSeries.subst β (MvPowerSeries.map σ (f k)) := by
    intro k; rw [expand_map_subst q hq σ hαS, hβ]
  have e2 : ∀ j, MvPowerSeries.subst α (f j - (p : K)⁻¹ •
      ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k))) =
      MvPowerSeries.subst α (f j) - (p : K)⁻¹ •
        ∑ k, M j k • MvPowerSeries.subst αq (MvPowerSeries.map σ (f k)) := by
    intro j
    rw [← MvPowerSeries.substAlgHom_apply hαS, map_sub, map_smul, map_sum]
    simp only [map_smul, MvPowerSeries.substAlgHom_apply, subst_expand q hq hαS, hαq]

  have hbr : ∀ k, Bd ‖(p : K)‖ (MvPowerSeries.subst αq (MvPowerSeries.map σ (f k)) -
      MvPowerSeries.subst β (MvPowerSeries.map σ (f k))) := by
    intro k
    apply bd_subst_sub _ αq β hαqS hβS (norm_nonneg _)
    intro n d
    obtain ⟨k', hk'dvd, hk'⟩ := hC K p q hq σ hS ι M hM ι f hf0 hfT k n
    rw [MvPowerSeries.coeff_map]
    have hs : ‖σ (MvPowerSeries.coeff n (f k))‖ * ‖(p : K)‖ ^ k' ≤ 1 := by
      have h0 : ‖MvPowerSeries.coeff n (f k) * (p : K) ^ k'‖ ≤ 1 := by
        rw [norm_mul, norm_pow]; exact hk'
      have h' := Formalism.LT.InverseIntegralClassesKeyFacts.norm_sigma_le_one hσ hp1' h0
      rwa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h'
    have hpow : ∀ i, Bd (‖(p : K)‖ ^ k' * ‖(p : K)‖) (αq i ^ n i - β i ^ n i) := by
      intro i
      obtain ⟨m, hm⟩ := hk'dvd i
      have hn : n i = p ^ (h * k') * m := by rw [hm, hqh, ← pow_mul]
      have hdiv1 : DivByMv ((p : K) ^ 1) (αq i - β i) := by simpa using hdiv i
      have h6 := Formalism.LT.PowCongr_valid K τ p hp (αq i) (β i) (hαqI i) (hβI i) 1 le_rfl hdiv1
        (h * k') m
      rw [← hn] at h6
      intro d'
      refine (h6 d').trans ?_
      rw [norm_pow, pow_add, pow_one, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg _) hp1' (Nat.le_mul_of_pos_left k' hh)) (norm_nonneg _)
    have hprod : Bd (‖(p : K)‖ ^ k' * ‖(p : K)‖)
        (n.prod (fun s e => αq s ^ e) - n.prod (fun s e => β s ^ e)) := by
      unfold Finsupp.prod
      exact bd_prod_sub (by positivity) (fun i => αq i ^ n i) (fun i => β i ^ n i) n.support
        (fun i _ => Formalism.FG.IntegralSubstitution.integral_pow (hαqI i) _)
        (fun i _ => Formalism.FG.IntegralSubstitution.integral_pow (hβI i) _) (fun i _ => hpow i)
    calc ‖σ (MvPowerSeries.coeff n (f k))‖ *
          ‖MvPowerSeries.coeff d (n.prod (fun s e => αq s ^ e) - n.prod (fun s e => β s ^ e))‖
        ≤ ‖σ (MvPowerSeries.coeff n (f k))‖ * (‖(p : K)‖ ^ k' * ‖(p : K)‖) :=
          mul_le_mul_of_nonneg_left (hprod d) (norm_nonneg _)
      _ = (‖σ (MvPowerSeries.coeff n (f k))‖ * ‖(p : K)‖ ^ k') * ‖(p : K)‖ := by ring
      _ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _

  intro j
  simp only [e3]
  have hgI : IntegralMv (MvPowerSeries.subst α (f j - (p : K)⁻¹ •
      ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k)))) :=
    Formalism.FG.integral_subst_vector K ι τ _ α (hfT j) hα0 hαI
  rw [e2] at hgI
  have e : MvPowerSeries.subst α (f j) - (p : K)⁻¹ •
        ∑ k, M j k • MvPowerSeries.subst β (MvPowerSeries.map σ (f k)) =
      (MvPowerSeries.subst α (f j) - (p : K)⁻¹ •
        ∑ k, M j k • MvPowerSeries.subst αq (MvPowerSeries.map σ (f k))) +
      (p : K)⁻¹ • ∑ k, M j k • (MvPowerSeries.subst αq (MvPowerSeries.map σ (f k)) -
        MvPowerSeries.subst β (MvPowerSeries.map σ (f k))) := by
    simp only [smul_sub, Finset.sum_sub_distrib]; abel
  rw [e]
  intro d
  rw [map_add, MvPowerSeries.coeff_smul, map_sum]
  refine norm_add_le_of (hgI d) ?_
  rw [norm_mul, norm_inv]
  have hsum : ‖∑ k, MvPowerSeries.coeff d (M j k • (MvPowerSeries.subst αq
      (MvPowerSeries.map σ (f k)) - MvPowerSeries.subst β (MvPowerSeries.map σ (f k))))‖ ≤
      ‖(p : K)‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k _ => ?_
    rw [MvPowerSeries.coeff_smul, norm_mul]
    calc _ ≤ 1 * ‖(p : K)‖ := mul_le_mul (hM j k) (hbr k d) (norm_nonneg _) zero_le_one
      _ = ‖(p : K)‖ := one_mul _
  calc ‖(p : K)‖⁻¹ * _ ≤ ‖(p : K)‖⁻¹ * ‖(p : K)‖ :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (norm_nonneg _))
    _ = 1 := inv_mul_cancel₀ hppos.ne'
end Formalism.FG.KeyVAux
