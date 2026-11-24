-- Prove2me | solution 1 for Formalism.LT.FunEqSubst_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:49.411429+00:00
-- url     : https://prove2.me/submissions/c88f9487-b339-4726-9156-0457c42c6799

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_finsum_le
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_add_le_of
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_sub_le_of
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_sigma_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT
open Formalism.G
open InverseIntegralClassesKeyFacts
namespace Formalism.LT
theorem _root_.solution (h4 : Formalism.LT.IntegralSubst.{u, v}) (h5 : Formalism.LT.CoeffBound.{u})
    (h6 : Formalism.LT.PowCongr.{u, v}) (h7 : Formalism.LT.FrobCongr.{u, v}) : Formalism.G.FunEqSubst.{u, v} := by
  intro K _ _ _ p q hq σ hS f hf0 hfT ι α hα0 hαI
  obtain ⟨hp, ⟨h, hh, hqh⟩, hp1, hσ⟩ := id hS
  have hp1' : ‖(p : K)‖ ≤ 1 := hp1.le
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hppos : 0 < ‖(p : K)‖ := norm_pos_iff.mpr hpne

  set fs : PowerSeries K := PowerSeries.map σ f with hfs
  set g : PowerSeries K := f - (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) with hg
  set β : MvPowerSeries ι K := MvPowerSeries.expand q hq (MvPowerSeries.map σ α) with hβ
  have hαS : PowerSeries.HasSubst α := HasSubst.of_constantCoeff_zero hα0
  have hαq0 : MvPowerSeries.constantCoeff (α ^ q) = 0 := by
    rw [map_pow, hα0, zero_pow hq]
  have hαqS : PowerSeries.HasSubst (α ^ q) := HasSubst.of_constantCoeff_zero hαq0
  have hmα0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ α) = 0 := by
    simp [hα0]
  have hmαS : PowerSeries.HasSubst (MvPowerSeries.map σ α) := HasSubst.of_constantCoeff_zero hmα0
  have hβ0 : MvPowerSeries.constantCoeff β = 0 := by
    rw [hβ, MvPowerSeries.constantCoeff_expand, hmα0]
  have hβS : PowerSeries.HasSubst β := HasSubst.of_constantCoeff_zero hβ0
  have hXqS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries K) ^ q) :=
    HasSubst.of_constantCoeff_zero' (by simp [hq])

  have hdec : f.subst α - (p : K)⁻¹ • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α))
      = g.subst α + (p : K)⁻¹ • (fs.subst (α ^ q) - fs.subst β) := by
    have e1 : f = g + (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) := by
      rw [hg]; abel
    have e2 : PowerSeries.subst α (fs.subst ((PowerSeries.X : PowerSeries K) ^ q) : PowerSeries K) = fs.subst (α ^ q) := by
      rw [PowerSeries.subst_comp_subst_apply hXqS hαS, PowerSeries.subst_pow hαS,
        PowerSeries.subst_X hαS]
    have e3 : MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α)) = fs.subst β := by
      rw [PowerSeries.map_subst hαS, PowerSeries.expand_subst q hq hmαS]
    have e4 : f.subst α = g.subst α + (p : K)⁻¹ • fs.subst (α ^ q) := by
      conv_lhs => rw [e1]
      rw [PowerSeries.subst_add hαS, PowerSeries.subst_smul hαS, e2]
    rw [e3, e4, smul_sub]; abel

  have hXqI : IntegralPS ((PowerSeries.X : PowerSeries K) ^ q) := by
    intro n
    rw [PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have hαqI : IntegralMv (α ^ q) := by
    have := h4 K ι _ α hXqI hα0 hαI
    rwa [PowerSeries.subst_pow hαS, PowerSeries.subst_X hαS] at this
  have hdiv : DivByMv (p : K) (α ^ q - β) := h7 K p q hq σ hS ι α hαI
  have hβI : IntegralMv β := by
    intro d
    have e : MvPowerSeries.coeff d β
        = MvPowerSeries.coeff d (α ^ q) - MvPowerSeries.coeff d (α ^ q - β) := by
      rw [map_sub]; ring
    rw [e]
    exact norm_sub_le_of (hαqI d) ((hdiv d).trans hp1')
  have hgI : IntegralMv (g.subst α) := h4 K ι g α hfT hα0 hαI

  have hbr : ∀ d, ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖ ≤ ‖(p : K)‖ := by
    intro d
    rw [map_sub, PowerSeries.coeff_subst hαqS, PowerSeries.coeff_subst hβS,
      ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hαqS fs d)
        (PowerSeries.coeff_subst_finite hβS fs d)]
    apply norm_finsum_le (norm_nonneg _)
    intro n
    rw [← smul_sub, ← map_sub, smul_eq_mul, norm_mul, hfs, PowerSeries.coeff_map]
    obtain ⟨k, hkdvd, hk⟩ := h5 K p q σ hS f hf0 hfT n
    obtain ⟨m, rfl⟩ := hkdvd
    have hn : q ^ k * m = p ^ (h * k) * m := by rw [hqh, ← pow_mul]
    have hdiv' : DivByMv ((p : K) ^ 1) (α ^ q - β) := by simpa using hdiv
    have hc0 := h6 K ι p hp (α ^ q) β hαqI hβI 1 le_rfl hdiv' (h * k) m d
    rw [← hn] at hc0
    have hs : ‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k ≤ 1 := by
      have h0 : ‖coeff (q ^ k * m) f * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]; exact hk
      have h' := norm_sigma_le_one hσ hp1' h0
      rwa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h'
    have hc : ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ := by
      refine hc0.trans ?_
      rw [norm_pow, pow_add, pow_one, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg _) hp1' (Nat.le_mul_of_pos_left k hh)) (norm_nonneg _)
    calc ‖σ (coeff (q ^ k * m) f)‖ * ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖σ (coeff (q ^ k * m) f)‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖) :=
          mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ = (‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ := by ring
      _ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _

  unfold IsFunEqTypeMv
  rw [hdec]
  intro d
  rw [map_add, MvPowerSeries.coeff_smul]
  refine norm_add_le_of (hgI d) ?_
  rw [norm_mul, norm_inv]
  calc ‖(p : K)‖⁻¹ * ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖
      ≤ ‖(p : K)‖⁻¹ * ‖(p : K)‖ := mul_le_mul_of_nonneg_left (hbr d) (inv_nonneg.mpr (norm_nonneg _))
    _ = 1 := inv_mul_cancel₀ hppos.ne'
end Formalism.LT
