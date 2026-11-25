-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.core2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:52.648729+00:00
-- url     : https://prove2.me/submissions/0183ddef-b4d7-4c7c-87e8-520e000f62d5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_UbTerms
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_NormUSum
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_norm_u_sum
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_u_disc
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_u_sum_re
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_akapD_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_eps_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_eps_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_exists_power_sum_lower_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_far_part
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_final_step
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_kap_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_kap_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_lb_part
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_rr_gt
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_th_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_turan_lb
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_ub_terms
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_x_part
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_akap_le__7038c74e9656


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (CT : ℝ) (a : ℕ) (hCT : 0 < CT) (ha : 1 ≤ a)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (CT * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (CF CP cZ cS c₁ c₂ : ℝ) (hCF : 0 < CF) (hCP : 0 < CP) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₁ : 0 < c₁)
    (hc₁Z : c₁ ≤ cZ / 4) (hc₂ : 0 < c₂)
    (hc₂κ : c₂ ≤ kap a (Real.log (max CT 1)) / (25 * CF))
    (hc₂P : c₂ ≤ th a / (2 * Real.exp 1 * CP * rr a))
    (L ℓ lam η Mr K : ℝ) (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam)
    (hηZ : cZ / (2 * L) ≤ η) (hηc : η ≤ c0 a) (hηL : η * L < c₂ * K) (hMr : 0 < Mr)
    (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hX : lam * L ^ 3 = c₁ * Real.exp (-K))
    (hK : K0 a (Real.log (max CT 1)) CP cZ cS c₁ < K)
    (N : ℕ) (w : Fin N → ℂ) (hw : ∀ i, η ≤ (w i).re) (hi0 : ∃ i, w i = ((η + η : ℝ) : ℂ))
    (hS : (∑ i, 1 / w i).re ≤ 2 * lam / η ^ 2 + CF * L * 25)
    (hpow : ∀ j : ℕ, 1 ≤ j → ‖∑ i, 1 / (w i) ^ j‖ ≤
        CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) :
    False := by
  set D := Real.log (max CT 1) with hD_def
  have hD : 0 ≤ D := Real.log_nonneg (le_max_right _ _)
  have hL0 : 0 < L := by linarith
  have hη : 0 < η := lt_of_lt_of_le (by positivity) hηZ
  have hr := rr_gt a
  have hr0 : 0 < rr a := by linarith
  have hε0 := eps_pos a
  have hε1 := eps_le a
  have hth := th_pos a
  have hκ := kap_pos a ha D hD
  have hκth := kap_le a ha D hD
  have hE0 : 0 < E0 a D := Real.exp_pos _
  have hG : 0 < GG a CP cZ cS c₁ := by unfold GG; positivity
  have hK0 : 0 < K0 a D CP cZ cS c₁ := by unfold K0; positivity
  have hKpos : 0 < K := lt_trans hK0 hK
  have hthK : E0 a D * GG a CP cZ cS c₁ < th a * K := by
    have h1 : K0 a D CP cZ cS c₁ * th a = E0 a D * GG a CP cZ cS c₁ := by unfold K0; field_simp
    have h2 : K0 a D CP cZ cS c₁ * th a < K * th a := mul_lt_mul_of_pos_right hK hth
    linarith only [h1, h2]
  have hexpK : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hXc : lam * L ^ 3 ≤ c₁ := by
    rw [hX]; have := mul_le_mul_of_nonneg_left hexpK hc₁.le; linarith only [this]
  have hlη1 : lam / η ≤ 2 * (lam * L) / cZ := by
    rw [div_le_div_iff₀ hη hcZ]
    have h1 : cZ ≤ 2 * L * η := by rw [div_le_iff₀ (by positivity)] at hηZ; linarith only [hηZ]
    have := mul_le_mul_of_nonneg_left h1 hlam.le
    linarith only [this]
  have hlamL : lam * L ≤ lam * L ^ 3 := by
    have h2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
    have h3 : L ≤ L ^ 3 := by
      have : L ^ 3 = L * L ^ 2 := by ring
      rw [this]; have := mul_le_mul_of_nonneg_left h2 hL0.le; linarith only [this]
    exact mul_le_mul_of_nonneg_left h3 hlam.le
  have hlη2 : lam / η ≤ 1 / 2 := by
    have h1 : 2 * (lam * L) / cZ ≤ 1 / 2 := by
      rw [div_le_iff₀ hcZ]; linarith only [hlamL, hXc, hc₁Z]
    linarith only [h1, hlη1]

  set u : Fin N → ℂ := fun i => (η : ℂ) / w i with hu_def
  have hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re := fun i => Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_disc η hη (w i) (hw i)
  have hi : ∃ i, 1 / 2 ≤ ‖u i‖ := by
    obtain ⟨i, hi⟩ := hi0
    refine ⟨i, ?_⟩
    simp only [hu_def, hi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη,
      abs_of_pos (by linarith : (0 : ℝ) < η + η)]
    rw [le_div_iff₀ (by linarith)]; linarith
  set S : ℝ := ∑ i, (u i).re with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => le_trans (by positivity) (hu i))
  have hS_eq : S = η * (∑ i, 1 / w i).re := by
    have := Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_sum_re η w 1
    simp only [pow_one] at this
    rw [hS_def, ← this, Complex.re_sum]
  have hSle : S ≤ 2 * (lam / η) + 25 * CF * (η * L) := by
    rw [hS_eq]
    have h2 := mul_le_mul_of_nonneg_left hS hη.le
    have h3 : η * (2 * lam / η ^ 2 + CF * L * 25) = 2 * (lam / η) + 25 * CF * (η * L) := by
      field_simp
    linarith only [h2, h3]
  have h25c : 25 * CF * c₂ ≤ kap a D := by
    rw [le_div_iff₀ (by positivity)] at hc₂κ; linarith only [hc₂κ]
  have hCFηL : 25 * CF * (η * L) ≤ kap a D * K := by
    have h1 : 25 * CF * (η * L) ≤ 25 * CF * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le (by positivity)
    have h2 := mul_le_mul_of_nonneg_right h25c hKpos.le
    linarith only [h1, h2]
  have hSK : S ≤ 1 + kap a D * K := by linarith only [hSle, hCFηL, hlη2]

  set m := ⌈th a * K⌉₊ with hm_def
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
    rw [hm_def]; exact (Nat.ceil_pos.mpr (by positivity)).ne')
  have hmle : (m : ℝ) < th a * K + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmge : th a * K ≤ m := Nat.le_ceil _
  obtain ⟨j, n, hmj, hjan, hn1, hnS, hLB⟩ :=
    exists_power_sum_lower_bound CT a hCT hT (eps a) hε0 (by linarith) N u hu hi m hm1
  have hjr1 : (m : ℝ) + 1 ≤ j := by exact_mod_cast hmj
  have hjr : th a * K < j := by linarith only [hjr1, hmge]
  have hj1 : 1 ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hnε : (n : ℝ) * eps a ^ 2 ≤ 1 + kap a D * K := le_trans hnS hSK
  have hjan' : (j : ℝ) ≤ m + a * n := by exact_mod_cast hjan
  have hjup : (j : ℝ) ≤ 2 * th a * K + j0 a := by
    have h1 : (a : ℝ) * n ≤ a / eps a ^ 2 + a * kap a D / eps a ^ 2 * K := by
      have : (n : ℝ) ≤ (1 + kap a D * K) / eps a ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hnε
      calc (a : ℝ) * n ≤ a * ((1 + kap a D * K) / eps a ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h2 : a * kap a D / eps a ^ 2 * K ≤ th a * K :=
      mul_le_mul_of_nonneg_right (akap_le' a ha D hD) hKpos.le
    unfold j0; linarith only [h1, h2, hjan', hmle]
  have hanD : (a : ℝ) * n * D ≤ a * D / eps a ^ 2 + j := by
    have h1 : (a : ℝ) * n * D = (a * D / eps a ^ 2) * (n * eps a ^ 2) := by field_simp
    have h2 := akapD_le a ha D hD
    have h3 : (a * D / eps a ^ 2) * (n * eps a ^ 2) ≤ (a * D / eps a ^ 2) * (1 + kap a D * K) :=
      mul_le_mul_of_nonneg_left hnε (by positivity)
    have h4 : (a * D / eps a ^ 2) * (1 + kap a D * K) = a * D / eps a ^ 2 + (a * D * kap a D / eps a ^ 2) * K := by ring
    have h5 := mul_le_mul_of_nonneg_right h2 hKpos.le
    linarith only [h1, h3, h4, h5, hjr]
  have hLB2 : 1 / (E0 a D * (rr a / 8) ^ j) ≤ ‖∑ i, u i ^ j‖ + eps a ^ (j - 2) * S :=
    le_trans (lb_part a D m n j _ (by omega) hanD (turan_lb CT hCT a n m hn1)) hLB

  have hU : ‖∑ i, u i ^ j‖ ≤ (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    have h1 : ‖∑ i, u i ^ j‖ = η ^ j * ‖∑ i, 1 / (w i) ^ j‖ := norm_u_sum η w j hη.le
    have h2 := mul_le_mul_of_nonneg_left (hpow j hj1) (pow_pos hη j).le
    have hc₂P' : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a := by
      rw [le_div_iff₀ (by positivity)] at hc₂P; linarith only [hc₂P]
    have h3 := ub_terms a CP CF cZ cS c₂ (kap a D) L ℓ lam η Mr K j hj1 hCP hCF hcZ hcS hc₂ hL hℓ0 hℓ hlam hη
      hMr hKpos hlη1 hM hηc hηL h25c hκth hc₂P' hjr
    rw [h1]; exact le_trans h2 h3
  have hF : eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j :=
    far_part a S j hj2 (by linarith only [hSK, hjr, mul_le_mul_of_nonneg_right hκth hKpos.le])
  have hXj := x_part a c₁ K hc₁ j hjup
  rw [← hX] at hXj
  set cA := 8 * CP / cZ + 4 / cZ + 32 * CP / cS with hcA
  have hcA0 : 0 ≤ cA := by positivity
  have hJ0 : 0 ≤ ((j : ℝ) + 1) ^ 2 := by positivity
  have hU2 : cA * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) ≤
      cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j) :=
    mul_le_mul_of_nonneg_left hXj (by positivity)
  have htot : 1 / (E0 a D * (rr a / 8) ^ j) ≤ GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    have : GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j =
        cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j + rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
      unfold GG; rw [hcA]; ring
    rw [this]; linarith only [hLB2, hU, hF, hU2]
  exact final_step a (E0 a D) (GG a CP cZ cS c₁) hE0 hG j (by linarith only [hthK, hjr]) htot
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
