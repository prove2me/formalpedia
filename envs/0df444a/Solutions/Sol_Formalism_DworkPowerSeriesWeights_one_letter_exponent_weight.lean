-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.one_letter_exponent_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:34.616398+00:00
-- url     : https://prove2.me/submissions/e86f8ed5-86cf-4420-b2bf-4cfbe325a564

import Definitions.Def_Formalism_GaussJetBounds_StatementR
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitsLogLoss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitFamily
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_lin_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_lin_wt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_one_le_norm_two
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_smul_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_smul_wt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_zmod2
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_single
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_monoWtGe_rad
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaS
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_oneLetterRadiusIdentity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_sum
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : OneLetterWt.{u, v} := by
  intro K _ _ _ l N0 N1 hl hodd hpi K0 hK0 ζ hζ be hbe ep hep ι _ M hM1 sgn hsgn
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hl3 : 3 ≤ l := by
    obtain ⟨k, hk⟩ := hodd
    have := hl.two_le
    omega
  obtain ⟨hOR1, hOR2⟩ := oneLetterRadiusIdentity l hl3
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hpi.le
  have hrho : 0 ≤ rho l := by
    unfold rho
    apply div_nonneg zero_le_one
    nlinarith
  have hrg : gam l = 1 / ((l : ℝ) - 1) - rho l := by
    have ha : (l : ℝ) - 1 ≠ 0 := by linarith
    have hb : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    unfold gam rho
    field_simp
    ring
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = rho l + 1 / ((l : ℝ) + 1) := ⟨_, rfl⟩
  have hRρ : rho l ≤ R := by
    have : 0 ≤ 1 / ((l : ℝ) + 1) := by positivity
    linarith
  obtain ⟨hS1, hS2⟩ := lemmaS K l 2 hl hodd le_rfl even_two hpi K0 hK0 ζ hζ be hbe
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra h
    have h' : MvPowerSeries.coeff 0 be ≠ 0 := by
      rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have := (hbe.2.2.1 0 h').1
    simp [degE] at this

  have hbeR : WtGe ‖(l : K)‖ (fun _ : ZMod 2 => R) (1 / ((l : ℝ) - 1)) be := by
    intro n
    by_cases hb : IsBiPower l n
    · obtain ⟨s, s', α, β, hs, hs', _, hsum, rfl⟩ := hb
      have hodd' : Odd (α + β) := by
        have key : ((α + β : ℕ) : ZMod 2) = 1 := by
          push_cast
          exact asmOne_zmod2 s s' _ _ hs hs' hsum
        exact ZMod.natCast_eq_one_iff_odd.mp key
      have hq := hOR1 α β hodd'
      have hn := hS1 (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))
      rw [monoWtGe_iff] at hn ⊢
      refine le_trans hn (Real.rpow_le_rpow_of_exponent_ge h0 h1 ?_)
      simp only [dot_add, asmR_dot_single, Nat.cast_pow]
      have e : (l : ℝ) ^ α * R + (l : ℝ) ^ β * R = (l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l +
          ((l : ℝ) ^ α + (l : ℝ) ^ β) / ((l : ℝ) + 1) := by
        rw [hR]; ring
      linarith
    · exact asmR_monoWtGe_rad h0 h1 (fun _ => hRρ) (hS2 n hb)

  have hc1 : ∀ s : ZMod 2, ‖(if s = 0 then (1 : K) else ep)‖ ≤ 1 := by
    intro s
    split_ifs
    · simp
    · exact hep.le
  have ha0 : ∀ (x : Fin N0 × Fin N1) (s : ZMod 2), MvPowerSeries.constantCoeff
      ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) = 0 :=
    fun x s => asmOne_smul_const _ (asmOne_lin_const _)
  have haw : ∀ (x : Fin N0 × Fin N1) (s : ZMod 2), WtGe ‖(l : K)‖ (fun _ : ι => R) R
      ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) :=
    fun x s => asmOne_smul_wt (hc1 s) (asmOne_lin_wt h0 (M x) (hM1 x) R)
  have hsub : ∀ x : Fin N0 × Fin N1, WtGe ‖(l : K)‖ (fun _ : ι => R) (1 / ((l : ℝ) - 1))
      (MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
        ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) :=
    fun x => substitution_weight_bound K ‖(l : K)‖ h0 hpi (ZMod 2) ι _ (fun _ => R) (fun _ => R) (1 / ((l : ℝ) - 1)) be
      (ha0 x) (haw x) hbeR
  have hsgn1 : ‖sgn / 2‖ ≤ 1 := by
    have hs1 : ‖sgn‖ = 1 := by rcases hsgn with h | h <;> simp [h]
    have h2 := asmOne_one_le_norm_two (K := K) hodd hpi
    rw [norm_div, hs1]
    exact (div_le_one (lt_of_lt_of_le one_pos h2)).mpr h2
  have hBw : WtGe ‖(l : K)‖ (fun _ : ι => R) (1 / ((l : ℝ) - 1))
      ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
        (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
          ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) :=
    asmOne_smul_wt hsgn1 (wtGe_sum h0 Finset.univ _ fun x _ => hsub x)
  have hBc : MvPowerSeries.constantCoeff
      ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
        (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
          ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) = 0 := by
    refine asmOne_smul_const _ ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (ha0 x)) (ha0 x) hbe0
  subst hR
  exact ⟨hBc, hBw⟩
end Formalism.DworkPowerSeriesWeights
