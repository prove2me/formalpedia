-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.final_smallness
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:32.809033+00:00
-- url     : https://prove2.me/submissions/3e132c42-d48c-4e3d-840d-d0ef87d201d0

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : FinalSmall := by
  intro C c hC hc
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, (2 * C) ^ (16 / c) + 1 ≤ k0 := exists_nat_ge _
  refine ⟨k0, ?_⟩
  intro k r f bb Cf Th hk hrf hbb hcf hlog hTh
  have h2C : 0 < 2 * C := by linarith
  have hrp := Real.rpow_nonneg h2C.le (16 / c)
  have hkR : (2 * C) ^ (16 / c) + 1 ≤ (k:ℝ) := le_trans hk0 (by exact_mod_cast hk)
  have hkpos : (0:ℝ) < k := by linarith
  have hk1 : (1:ℝ) ≤ k := by linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (k:ℝ) ^ (c / 16) := ⟨_, rfl⟩
  have hT2C : 2 * C ≤ T := by
    have h1 : ((2 * C) ^ (16 / c)) ^ (c / 16) ≤ (k:ℝ) ^ (c / 16) :=
      Real.rpow_le_rpow hrp (by linarith) (by positivity)
    rw [← Real.rpow_mul h2C.le, show 16 / c * (c / 16) = 1 by field_simp, Real.rpow_one] at h1
    rw [hT]; exact h1
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hkc : (k:ℝ) ^ c = T ^ 16 := by
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]; congr 1; push_cast; field_simp
  have hThpos : 0 < Th := lt_of_lt_of_le (by rw [hkc]; positivity) hTh
  have hu : C / Th ≤ (2 * T ^ 15)⁻¹ := by
    rw [div_le_iff₀ hThpos]
    calc C ≤ T / 2 := by linarith
      _ = (2 * T ^ 15)⁻¹ * T ^ 16 := by field_simp; try ring
      _ ≤ (2 * T ^ 15)⁻¹ * Th := mul_le_mul_of_nonneg_left (by rw [← hkc]; exact hTh) (by positivity)
  have hu0 : 0 ≤ C / Th := by positivity
  have huf : (C / Th) ^ f ≤ ((2 * T ^ 15)⁻¹) ^ f := pow_le_pow_left₀ hu0 hu f
  have hlogbb : Real.log bb ≤ f * Real.log T := by
    rw [hT, Real.log_rpow hkpos]
    have hlogk0 : 0 ≤ Real.log k := Real.log_nonneg hk1
    have hlb0 : 0 ≤ Real.log bb := Real.log_nonneg hbb
    have h1 : 16 * Real.log bb ≤ c * Cf * Real.log bb := mul_le_mul_of_nonneg_right hcf hlb0
    have h2 : c * (Cf * Real.log bb) ≤ c * (f * Real.log k) := mul_le_mul_of_nonneg_left hlog hc.le
    nlinarith
  have hbbT : bb ≤ T ^ f := by
    have : Real.log bb ≤ Real.log (T ^ f) := by rw [Real.log_pow]; exact hlogbb
    exact (Real.log_le_log_iff (by linarith) (by positivity)).mp this
  have hf2 : 2 ≤ f := by omega
  have hr1 : ((r:ℝ) + 1) ≤ 2 ^ f := by
    have : r + 1 < 2 ^ f := lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
    exact_mod_cast this.le
  have hCT : C ≤ T := by linarith
  have hTf : T ≤ T ^ (8 * f) := le_self_pow₀ hT1 (by omega)
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hCr : C * ((r:ℝ) + 1) ≤ T ^ (8 * f) * 2 ^ f :=
    mul_le_mul (le_trans hCT hTf) hr1 (by linarith) (by positivity)
  have hbb7 : (bb ^ 7)⁻¹ ≥ ((T ^ f) ^ 7)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hbbT 7)
  have hmain : C * ((r:ℝ) + 1) * (C / Th) ^ f ≤ (bb ^ 7)⁻¹ := by
    calc C * ((r:ℝ) + 1) * (C / Th) ^ f ≤ (T ^ (8 * f) * 2 ^ f) * ((2 * T ^ 15)⁻¹) ^ f :=
          mul_le_mul hCr huf (by positivity) (by positivity)
      _ = ((T ^ f) ^ 7)⁻¹ := by
          rw [inv_pow, mul_pow, ← pow_mul, ← pow_mul]; field_simp; ring
      _ ≤ (bb ^ 7)⁻¹ := hbb7
  refine ⟨?_, hmain⟩
  have h1 : (bb ^ 7)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hbb)
  have h2 : (r:ℝ) * (C / Th) ^ f ≤ C * ((r:ℝ) + 1) * (C / Th) ^ f := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  linarith
end Formalism.FourierDecayAlt.P
