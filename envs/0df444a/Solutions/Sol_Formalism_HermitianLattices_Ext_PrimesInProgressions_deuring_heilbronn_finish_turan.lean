-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.deuring_heilbronn_finish_turan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:15.941972+00:00
-- url     : https://prove2.me/submissions/6be4e85c-fbb4-425c-a741-71377bd44e19

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinish
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_NormUSum
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnFinishTuran
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_logMT_ge_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_region_gap
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_core2
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_kap_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_log_sq_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_rr_gt
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_th_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_twentyFive_mul_smallConstant
import Theorems.Thm_Formalism_ZeroFreeDirichlet_excBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
set_option maxHeartbeats 1000000
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : DHFinish2Of := by
  intro hTur hIneq hPrime
  obtain ⟨CT, a, hCT, ha, hT2⟩ := hTur
  obtain ⟨CF, hCF, hF⟩ := hIneq
  obtain ⟨CP, hCP, hP⟩ := hPrime
  obtain ⟨cS, hcS, hE⟩ := excBound (1 / 2) (by norm_num)
  obtain ⟨cZ, hcZ, hG⟩ := DHF.region_gap
  have hD0 : 0 ≤ Real.log (max CT 1) := Real.log_nonneg (le_max_right _ _)
  obtain ⟨c₁, hc₁pos, hc₁Z, hc₁20⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ cZ / 4 ∧ c ≤ 1 / 20 :=
    ⟨min (cZ / 4) (1 / 20), lt_min (by linarith) (by norm_num), min_le_left _ _, min_le_right _ _⟩
  have hrr : 16 < TuranPowerSumBounds.rr a := TuranPowerSumBounds.rr_gt a
  obtain ⟨c₂, hc₂pos, hc₂k, hc₂t, hc₂K⟩ : ∃ c : ℝ, 0 < c ∧
      c ≤ TuranPowerSumBounds.kap a (Real.log (max CT 1)) / (25 * CF) ∧
      c ≤ TuranPowerSumBounds.th a / (2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a) ∧
      c * (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) ≤ cZ := by
    have hk := div_pos (TuranPowerSumBounds.kap_pos a ha _ hD0) (by positivity : (0 : ℝ) < 25 * CF)
    have ht := div_pos (TuranPowerSumBounds.th_pos a) (by positivity : (0 : ℝ) < 2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a)
    have hq : (0 : ℝ) < 2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) := by positivity
    refine ⟨min (min (TuranPowerSumBounds.kap a (Real.log (max CT 1)) / (25 * CF))
      (TuranPowerSumBounds.th a / (2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a)))
      (cZ / (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1))),
      lt_min (lt_min hk ht) (div_pos hcZ hq),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_⟩
    rw [← le_div_iff₀ hq]
    exact min_le_right _ _
  have hc0pos : 0 < TuranPowerSumBounds.c0 a := by
    have := TuranPowerSumBounds.twentyFive_mul_smallConstant a
    have : 0 < 1 / TuranPowerSumBounds.rr a := by positivity
    linarith
  have hc0 : TuranPowerSumBounds.c0 a ≤ 1 / 25 := by
    have := TuranPowerSumBounds.twentyFive_mul_smallConstant a
    have h1 : 1 / TuranPowerSumBounds.rr a ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  refine ⟨TuranPowerSumBounds.c0 a, c₁, c₂, 3, hc0pos, hc₁pos, hc₂pos, ?_⟩
  intro M _ χ₁ χ β₁ T ρ hM hT hsq hne1 hL hβ hβ1 hρ hre hIm hne
  have hL1 : 1 ≤ Real.log ((M : ℝ) * T) := DHF.logMT_ge_one M T hM hT
  have hLpos : 0 < Real.log ((M : ℝ) * T) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hgap := hG M χ₁ χ β₁ T c₁ ρ hM hT hne1 hL hc₁pos (by linarith) hβ hρ hIm hne
  have hη : 0 < 1 - ρ.re := by
    by_contra h
    push_neg at h
    nlinarith
  have hηZ : cZ / (2 * Real.log ((M : ℝ) * T)) ≤ 1 - ρ.re := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hηc0 : 1 - ρ.re ≤ TuranPowerSumBounds.c0 a := by linarith
  have hlam : 0 < 1 - β₁ := by linarith
  have hEx := hE M χ₁ β₁ hsq hne1 hL
  have hs : 0 < √(M : ℝ) := Real.sqrt_pos.mpr hMpos
  have hmm : √(M : ℝ) * √(M : ℝ) = M := Real.mul_self_sqrt hMpos.le
  have hsqrt : (M : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / √(M : ℝ) := by
    rw [Real.rpow_neg hMpos.le, ← Real.sqrt_eq_rpow, one_div]
  have hcs : cS ≤ (1 - β₁) * √(M : ℝ) := by
    rw [hsqrt] at hEx
    have h1 : cS * (1 / √(M : ℝ)) ≤ 1 - β₁ := by linarith
    rw [mul_one_div, div_le_iff₀ hs] at h1
    exact h1
  have hℓ0 : 0 ≤ Real.log (3 * (M : ℝ)) := Real.log_nonneg (by linarith)
  have hℓpos : 0 < Real.log (3 * (M : ℝ)) := Real.log_pos (by linarith)
  have hℓL : Real.log (3 * (M : ℝ)) ≤ 2 * Real.log ((M : ℝ) * T) := by
    have hT4 : (4 : ℝ) ≤ T ^ 2 := by nlinarith
    have h3 : 3 * (M : ℝ) ≤ ((M : ℝ) * T) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hT4 (sq_nonneg (M : ℝ))]
    calc Real.log (3 * (M : ℝ)) ≤ Real.log (((M : ℝ) * T) ^ 2) :=
          Real.log_le_log (by linarith) h3
      _ = 2 * Real.log ((M : ℝ) * T) := by
          rw [Real.log_pow]
          push_cast
          ring
  have hℓM : Real.log (3 * (M : ℝ)) ^ 2 / (M : ℝ) ≤ 32 * (1 - β₁) / cS := by
    rw [div_le_div_iff₀ hMpos hcS]
    have hls := TuranPowerSumBounds.log_sq_bound (M : ℝ) (by linarith)
    calc Real.log (3 * (M : ℝ)) ^ 2 * cS ≤ 32 * √(M : ℝ) * cS :=
          mul_le_mul_of_nonneg_right hls hcS.le
      _ ≤ 32 * √(M : ℝ) * ((1 - β₁) * √(M : ℝ)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = 32 * (1 - β₁) * (M : ℝ) := by linear_combination (32 * (1 - β₁)) * hmm
  rw [div_le_iff₀ hLpos]
  by_contra hcon
  push_neg at hcon
  have hKK0 : TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁ <
      Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)) := by
    by_contra h
    push_neg at h
    have h1 : c₂ * Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)) ≤
        c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self (TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁)])
        hc₂pos.le
    have h3 : c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) ≤ cZ / 2 := by
      have e : c₂ * (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) =
          2 * (c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) := by ring
      linarith
    linarith
  have hpos : 0 < c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3) := by positivity
  have hexp : (1 - β₁) * Real.log ((M : ℝ) * T) ^ 3 =
      c₁ * Real.exp (-Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3))) := by
    rw [Real.exp_neg, Real.exp_log hpos]
    field_simp
  have hρre : (22 / 25 : ℝ) ≤ ρ.re := by linarith
  have hβ20 : (19 / 20 : ℝ) ≤ β₁ := by
    have : c₁ / Real.log ((M : ℝ) * T) ≤ 1 / 20 := by
      rw [div_le_iff₀ hLpos]
      nlinarith
    linarith
  obtain ⟨N, w, hwre, hwex, hwsum, hwj⟩ := hF M χ₁ χ β₁ T (1 - ρ.re) ρ hM hT hsq hne1 hL hβ20 hβ1
    hρ hρre hIm hne hη (by linarith)
  have hβP : 1 - 1 / Real.log (3 * (M : ℝ)) ≤ β₁ := by
    have : c₁ / Real.log ((M : ℝ) * T) ≤ 1 / Real.log (3 * (M : ℝ)) := by
      rw [div_le_div_iff₀ hLpos hℓpos]
      nlinarith
    linarith
  refine TuranPowerSumBounds.core2 CT a hCT ha hT2 CF CP cZ cS c₁ c₂ hCF hCP hcZ hcS hc₁pos hc₁Z hc₂pos hc₂k hc₂t
    (Real.log ((M : ℝ) * T)) (Real.log (3 * (M : ℝ))) (1 - β₁) (1 - ρ.re) (M : ℝ)
    (Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)))
    hL1 hℓ0 hℓL hlam hηZ hηc0 hcon hMpos hℓM hexp hKK0 N w hwre hwex hwsum ?_
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 := hwj (i + 1) hj
  have h2 := hP M χ₁ β₁ (1 + (1 - ρ.re)) i hM hsq hne1 hL hβP hβ1 (by linarith) (by linarith)
  simp only [Nat.add_sub_cancel] at h1 ⊢
  have e1 : (1 + (1 - ρ.re)) - 1 = 1 - ρ.re := by ring
  rw [e1] at h2
  have hA : CP * (1 - β₁) * Real.log (3 * (M : ℝ)) ^ 2 * ((i : ℝ) + 2) ^ 2 / (1 - ρ.re) ^ (i + 2) =
      CP * (1 - β₁) * Real.log (3 * (M : ℝ)) ^ 2 * (((i + 1 : ℕ) : ℝ) + 1) ^ 2 /
        (1 - ρ.re) ^ (i + 1 + 1) := by
    push_cast
    ring_nf
  have hC : CP * ((i : ℝ) + 2) * Real.log (3 * (M : ℝ)) ^ 2 / ((M : ℝ) * (1 - ρ.re) ^ (i + 1)) =
      CP * (((i + 1 : ℕ) : ℝ) + 1) * Real.log (3 * (M : ℝ)) ^ 2 / ((M : ℝ) * (1 - ρ.re) ^ (i + 1)) := by
    push_cast
    ring_nf
  rw [hA, hC] at h2
  exact h1.trans (add_le_add (add_le_add h2 le_rfl) le_rfl)
end Formalism.HermitianLattices.Ext.PrimesInProgressions
