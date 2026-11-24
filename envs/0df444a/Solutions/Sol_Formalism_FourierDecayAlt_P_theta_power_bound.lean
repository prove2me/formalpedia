-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.theta_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:40.337973+00:00
-- url     : https://prove2.me/submissions/7202577d-fb58-4d80-900c-097bd0ef531a

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_delLower
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_sqrtTTLower
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_quantOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_quantitative_fourth_power_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_quantThree

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
set_option maxHeartbeats 800000
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : ThetaPower := by
  intro C A0 Ct CDel cT Cb hC hA0 hCt hCDel hcT hCb hcb
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, max (max (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))) (Real.exp (2 / Cb)) + 4 ≤ k0 :=
    exists_nat_ge _
  refine ⟨k0, ?_⟩
  intro k m f bb N I Del TT hk hm hmf hfk hN hI hbb hDel hTT
  have hkR : (k0:ℝ) ≤ k := by exact_mod_cast hk
  have m1 := le_max_left (max (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))) (Real.exp (2 / Cb))
  have m2 := le_max_right (max (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))) (Real.exp (2 / Cb))
  have m3 := le_max_left (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))
  have m4 := le_max_right (max (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0)))
      (max ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi))
  have m5 := le_max_left (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))
  have m6 := le_max_right (1000 * (Ct * C * A0) ^ 2) (40 * (Real.pi * Ct * C ^ 2 * A0))
  have m7 := le_max_left ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi)
  have m8 := le_max_right ((Real.pi * Ct * C * A0) ^ 2) (40 * C * Real.pi)
  have hpi := Real.pi_pos
  have hexp := Real.exp_pos (2 / Cb)
  have hkW : 1000 * (Ct * C * A0) ^ 2 ≤ k := by linarith
  have hkV : 40 * (Real.pi * Ct * C ^ 2 * A0) ≤ k := by linarith
  have hkM : (Real.pi * Ct * C * A0) ^ 2 ≤ k := by linarith
  have hkC : 40 * C * Real.pi ≤ k := by linarith
  have hke : Real.exp (2 / Cb) ≤ k := by linarith
  have hk4 : (4:ℝ) ≤ k := by nlinarith [sq_nonneg (Ct * C * A0)]
  have hk1 : (1:ℝ) ≤ k := by linarith
  have hkpos : (0:ℝ) < k := by linarith
  have hk1N : 1 ≤ k := by exact_mod_cast hk1
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmf' : (m:ℝ) ≤ f := by exact_mod_cast hmf
  have hfk' : (f:ℝ) ≤ k := by exact_mod_cast hfk
  have hf1 : (1:ℝ) ≤ f := by linarith
  have hf1N : 1 ≤ f := by omega
  have hbbpos : 0 < bb := lt_of_lt_of_le (Real.rpow_pos_of_pos hkpos _) hbb
  have hlogk : 2 / Cb ≤ Real.log k := by
    rw [← Real.log_exp (2 / Cb)]; exact Real.log_le_log (Real.exp_pos _) hke
  have hlb : 1 ≤ Real.log bb := by
    have h1 : Real.log ((k:ℝ) ^ (Cb / 2)) ≤ Real.log bb :=
      Real.log_le_log (Real.rpow_pos_of_pos hkpos _) hbb
    rw [Real.log_rpow hkpos] at h1
    have h3 : Cb / 2 * (2 / Cb) = 1 := by field_simp
    have h2 : Cb / 2 * (2 / Cb) ≤ Cb / 2 * Real.log k := mul_le_mul_of_nonneg_left hlogk (by positivity)
    linarith
  have hD := Sz8.delLower k f (Real.log bb) CDel Del hk1N hf1N hlb hCDel hDel
  have hf4 : 1 ≤ (f:ℝ) ^ 4 := one_le_pow₀ hf1
  have hK1 : 1 ≤ (k:ℝ) ^ (CDel - 4) := Real.one_le_rpow hk1 (by linarith)
  have hk4D : (k:ℝ) ^ 4 ≤ Del := by
    have h1 : (1:ℝ) * 1 ≤ (f:ℝ) ^ 4 * (k:ℝ) ^ (CDel - 4) := mul_le_mul hf4 hK1 zero_le_one (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hkpos.le 4)
    have e : (k:ℝ) ^ 4 * ((f:ℝ) ^ 4 * (k:ℝ) ^ (CDel - 4)) = (k:ℝ) ^ 4 * (f:ℝ) ^ 4 * (k:ℝ) ^ (CDel - 4) := by ring
    linarith
  have hk2 : 16 * (k:ℝ) ^ 2 ≤ (k:ℝ) ^ 4 := by
    have h16 : (16:ℝ) ≤ (k:ℝ) ^ 2 := by nlinarith
    calc 16 * (k:ℝ) ^ 2 ≤ (k:ℝ) ^ 2 * (k:ℝ) ^ 2 := mul_le_mul_of_nonneg_right h16 (sq_nonneg _)
      _ = (k:ℝ) ^ 4 := by ring
  have hk256 : (256:ℝ) ≤ (k:ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hk4 4; norm_num at this; linarith
  have hI4 : Del / 4 ≤ I := by rw [hI]; linarith
  have hIpos : 0 < I := by linarith
  have he2a : 2 * cExp CDel cT Cb ≤ CDel - 4 := by
    unfold cExp; have := min_le_left ((CDel - 4) / 2) ((cT * Cb - 1) / 4); linarith
  have he2b : 2 * cExp CDel cT Cb ≤ cT * Cb - 1 := by
    unfold cExp; have := min_le_right ((CDel - 4) / 2) ((cT * Cb - 1) / 4); linarith
  have he0 : 0 ≤ cExp CDel cT Cb := by
    unfold cExp
    have : 0 ≤ min ((CDel - 4) / 2) ((cT * Cb - 1) / 4) := le_min (by linarith) (by linarith)
    linarith
  have hP2 : ((k:ℝ) ^ cExp CDel cT Cb) ^ 2 = (k:ℝ) ^ (2 * cExp CDel cT Cb) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]; congr 1; push_cast; ring
  have hNk : N ≤ 10 * k := by rw [hN]; linarith
  refine ⟨?_, ?_⟩
  · rw [div_le_one hIpos]
    have hN0 : 0 ≤ N := by rw [hN]; positivity
    have h1 : C * Real.pi * N ≤ C * Real.pi * (10 * k) := mul_le_mul_of_nonneg_left hNk (by positivity)
    have h2 : 40 * C * Real.pi * k ≤ (k:ℝ) * k := mul_le_mul_of_nonneg_right hkC hkpos.le
    have hkk : (k:ℝ) * k = (k:ℝ) ^ 2 := by ring
    linarith
  · refine le_min (le_min ?_ ?_) ?_
    · have := Sz8.quantOne k f m ((k:ℝ) ^ (CDel - 4)) ((k:ℝ) ^ cExp CDel cT Cb) (Ct * C * A0) Del
        hk1 (by linarith) hmf' hf1 (by rw [hP2]; exact Real.rpow_le_rpow_of_exponent_le hk1 he2a)
        (by positivity) hkW hD
      rw [hN]; exact this
    · have hsk : Real.sqrt k ≤ k := by
        calc Real.sqrt k ≤ Real.sqrt ((k:ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ = k := Real.sqrt_sq hkpos.le
      have := Sz8.quantitative_fourth_power_bound k f m ((k:ℝ) ^ (CDel - 4)) ((k:ℝ) ^ cExp CDel cT Cb)
        (Real.pi * Ct * C ^ 2 * A0) (Real.sqrt k) Del hk1 (by linarith) hmf' hf1 (by positivity)
        (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) (by positivity) hkV (Real.sqrt_nonneg _) hsk hD
      have hsk0 : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
      rw [le_div_iff₀ (by rw [hN]; positivity)]
      have e : (k:ℝ) ^ cExp CDel cT Cb * (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) =
          (k:ℝ) ^ cExp CDel cT Cb * (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * (10 * m)) := by rw [hN]
      rw [e]; linarith
    · have hS := Sz8.sqrtTTLower k bb cT Cb m TT hk1 hcT hCb hm2 hbb hTT
      exact Sz8.quantThree k ((k:ℝ) ^ (cT * Cb - 1)) ((k:ℝ) ^ cExp CDel cT Cb) (Real.pi * Ct * C * A0)
        (Real.sqrt TT) hk1 (by rw [hP2]; exact Real.rpow_le_rpow_of_exponent_le hk1 he2b)
        (by positivity) hkM hS
end Formalism.FourierDecayAlt.P
