-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DeIntegral_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:26:41.648424+00:00
-- url     : https://prove2.me/submissions/6e9895b6-c033-4454-b131-50ddd1e783d2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_IntegralPderivLgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_p_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_integral_pderiv_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_natCast
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_sm_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_g_zero_relation_holds


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_mul bd_C bd_sum int_mul int_pow sm_mul bd_natCast frob_congr
  PhiH PhiH_apply)
open DividedPowerNorms
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hD : DivDeriv) (hL : LawSymm) : DeIntegral := by
  intro K _ _ _ p σ hp hnp hσ F hF
  have hσF : MvPowerSeries.map σ F = F := (hL K p hp hnp F hF).1 σ
  obtain ⟨hF0, hFi, hFc⟩ := hF
  have hpK : (p : K) ≠ 0 := norm_pos_iff.mp (norm_p_pos hp hnp)
  have hg0 := (g_zero_relation_holds K p hp.two_le hpK).1
  have hsXp : PowerSeries.HasSubst (PowerSeries.X ^ p : PowerSeries K) :=
    PowerSeries.HasSubst.X_pow hp.ne_zero
  have hsF : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have hsX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.X i
  have hsP : MvPowerSeries.HasSubst
      (fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ^ p) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp [hp.ne_zero]

  have key : ∀ a : MvPowerSeries (Fin 2) K, PowerSeries.HasSubst a →
      PowerSeries.subst a (g0F K p) =
        MvPowerSeries.C ((p : K)⁻¹) * PowerSeries.subst (a ^ p) (lgF K p) := by
    intro a ha
    rw [hg0, PowerSeries.subst_mul ha, PowerSeries.subst_C,
      PowerSeries.subst_comp_subst_apply hsXp ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

  have key2 : ∀ a : MvPowerSeries (Fin 2) K, PowerSeries.HasSubst a →
      frobVar p (PowerSeries.subst a (lgF K p)) = PowerSeries.subst (frobVar p a) (lgF K p) := by
    intro a ha
    unfold frobVar
    rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha.const hsP]
    rfl
  have hX : ∀ i : Fin 2, frobVar p (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X i ^ p := fun i => by
    unfold frobVar
    rw [MvPowerSeries.subst_X hsP]
  have hat : ∀ i : Fin 2, at1 i (g0F K p) =
      MvPowerSeries.C ((p : K)⁻¹) * frobVar p (at1 i (lgF K p)) := fun i => by
    unfold at1
    rw [key _ (hsX i), key2 _ (hsX i), hX]
  have hlog : PowerSeries.subst F (lgF K p) = at1 0 (lgF K p) + at1 1 (lgF K p) := by
    unfold cob at hFc
    linear_combination hFc
  have hsum : at1 0 (g0F K p) + at1 1 (g0F K p) =
      MvPowerSeries.C ((p : K)⁻¹) * PowerSeries.subst (frobVar p F) (lgF K p) := by
    rw [← key2 F hsF, hlog, hat, hat, frobVar_eq_expand hp.ne_zero, frobVar_eq_expand hp.ne_zero,
      frobVar_eq_expand hp.ne_zero, map_add, mul_add]

  set r : MvPowerSeries (Fin 2) K := MvPowerSeries.C ((p : K)⁻¹) * (frobVar p F - F ^ p) with hr
  have hCC : MvPowerSeries.C (p : K) * MvPowerSeries.C ((p : K)⁻¹) =
      (1 : MvPowerSeries (Fin 2) K) := by
    rw [← map_mul, mul_inv_cancel₀ hpK, map_one]
  have hFr : frobVar p F = F ^ p + MvPowerSeries.C (p : K) * r := by
    rw [hr, ← mul_assoc, hCC]
    ring
  have hinv : ‖((p : K)⁻¹)‖ = (p : ℝ) := by rw [norm_inv, hnp, inv_inv]
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hscale : ∀ f : MvPowerSeries (Fin 2) K, Bd (p : ℝ)⁻¹ f →
      Integral (MvPowerSeries.C ((p : K)⁻¹) * f) := by
    intro f hf n
    rw [MvPowerSeries.coeff_C_mul, norm_mul, hinv]
    calc (p : ℝ) * ‖MvPowerSeries.coeff n f‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (hf n) hppos.le
      _ = 1 := mul_inv_cancel₀ hppos.ne'
  have hri : Integral r := by
    refine hscale _ fun n => ?_
    have h := frob_congr (σ := σ) hp hnp hσ (f := F) hFi n
    rw [PhiH_apply, hσF, map_sub, norm_sub_rev, ← map_sub] at h
    exact h
  have hr0 : MvPowerSeries.constantCoeff r = 0 := by
    have h1 : MvPowerSeries.constantCoeff (frobVar p F) = 0 := by
      have := coeff_frobVar_smul hp.ne_zero F 0
      rw [smul_zero] at this
      simpa [hF0] using this
    rw [hr, map_mul, map_sub, h1, map_pow, hF0, zero_pow hp.ne_zero, sub_zero, mul_zero]
  have hmain := hD K Unit (Fin 2) p hp hnp () (lgF K p) (fun _ => F ^ p) r
    (integral_pderiv_lgF hp hnp) (fun _ => by rw [map_pow, hF0, zero_pow hp.ne_zero])
    (fun _ => int_pow hFi p) hr0 hri
  have hupd : Function.update (fun _ : Unit => F ^ p) () (F ^ p + MvPowerSeries.C (p : K) * r) =
      fun _ => frobVar p F := by
    funext u
    simp [hFr]
  rw [hupd] at hmain
  have e : cob F (g0F K p) = MvPowerSeries.C ((p : K)⁻¹) *
      (-(MvPowerSeries.subst (fun _ : Unit => frobVar p F) (lgF K p : MvPowerSeries Unit K) -
        MvPowerSeries.subst (fun _ : Unit => F ^ p) (lgF K p : MvPowerSeries Unit K))) := by
    unfold cob
    rw [sub_sub, hsum, key F hsF, PowerSeries.subst_def, PowerSeries.subst_def]
    ring
  rw [e]
  exact hscale _ (DworkIntegrality.bd_neg hmain)
end Formalism.InvariantFactorPaths.G7
