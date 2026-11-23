-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:15.586926+00:00
-- url     : https://prove2.me/submissions/f0b55740-1501-4034-b363-75cb8326d866

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_D3_hpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
theorem _root_.solution (A : ℕ) (CB CSt Cg CT : ℝ) (_hCB : 0 ≤ CB) (hCSt : 0 ≤ CSt) (hCg : 0 ≤ Cg) (hCT : 0 ≤ CT)
    (r f : ℕ) (b rd g TT cSt e1 m M : ℝ) (hm : m = 2 * (r : ℝ) + 2) (hM : M = m ^ 5 * f)
    (hf : 1 ≤ f) (hb : 16 ≤ b) (hrd0 : 0 < rd) (hrd : rd ≤ b) (hg1 : 1 ≤ g) (hg : g ≤ b ^ Cg)
    (hTT0 : 0 < TT) (hTT : TT ≤ b ^ (2 * CT * m)) (hc0 : 0 ≤ cSt) (hc : cSt ≤ b ^ (CSt * m ^ 3 * f))
    (he0 : 0 ≤ e1) (he : e1 ≤ 2) :
    (64 : ℝ) ^ (f * (r + 1)) * (cSt * e1 * (rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f)) *
          (g ^ f) ^ (A * (r + 1) ^ 2) * Real.exp (CB * M * Real.log b)) *
        ((rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3))) ≤
      Real.exp ((2 + CSt + 1 + 12 + 12 * CT + Cg * A + CB + 1 + Cg) * M * Real.log b) := by
  have hb1 : (1 : ℝ) < b := by linarith
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hF : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hF0 : (0 : ℝ) ≤ f := by linarith
  have hg0 : (0 : ℝ) ≤ g := by linarith
  have hm2 : (2 : ℝ) ≤ m := by rw [hm]; linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hsq : (4 : ℝ) ≤ m ^ 2 := by
    have := mul_le_mul hm2 hm2 (by norm_num) hm0
    linarith
  have h3 : (8 : ℝ) ≤ m ^ 3 := by
    have := mul_le_mul hsq hm2 (by norm_num) (by positivity)
    linarith
  have h4 : (16 : ℝ) ≤ m ^ 4 := by
    have := mul_le_mul hsq hsq (by norm_num) (by positivity)
    linarith
  have h15 : m ≤ m ^ 5 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ m ^ 4 by linarith) hm0
    linarith
  have h25 : m ^ 2 ≤ m ^ 5 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ m ^ 3 by linarith) (pow_nonneg hm0 2)
    linarith
  have h35 : m ^ 3 ≤ m ^ 5 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ m ^ 2 by linarith) (pow_nonneg hm0 3)
    linarith
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    have := mul_le_mul_of_nonneg_left hF (pow_nonneg hm0 5)
    linarith
  have hRm : (r : ℝ) + 1 ≤ m := by rw [hm]; linarith
  have hRR : (r : ℝ) * (r + 1) ≤ m ^ 2 := by rw [hm]; linarith [sq_nonneg (r : ℝ)]
  have hR2 : ((r : ℝ) + 1) ^ 2 ≤ m ^ 2 := by rw [hm]; linarith [sq_nonneg (r : ℝ)]
  have hR3 : ((r : ℝ) + 1) * (2 * r + 3) ≤ m ^ 2 := by rw [hm]; linarith [sq_nonneg (r : ℝ)]
  have h64 : (64 : ℝ) ^ (f * (r + 1)) ≤ Real.exp (2 * M * Real.log b) :=
    hpow hb1 (by norm_num) (by
      rw [Real.rpow_two]
      have := mul_le_mul hb hb (by norm_num) (by linarith)
      linarith) _
      (by push_cast; rw [hM]; linarith [mul_le_mul_of_nonneg_right (hRm.trans h15) hF0])
  have hcS : cSt ≤ Real.exp (CSt * M * Real.log b) := by
    have h := hpow hb1 hc0 hc 1 (K := CSt) (M := M)
      (by push_cast; rw [hM]; linarith [mul_nonneg (mul_nonneg hCSt (sub_nonneg.2 h35)) hF0])
    rwa [pow_one] at h
  have he1 : e1 ≤ Real.exp (1 * M * Real.log b) := by
    have h := hpow hb1 he0 (show e1 ≤ b ^ (1 : ℝ) by rw [Real.rpow_one]; linarith) 1 (K := 1) (M := M)
      (by push_cast; linarith)
    rwa [pow_one] at h
  have hrdb : rd ^ (12 * r * (r + 1) * f) ≤ Real.exp (12 * M * Real.log b) :=
    hpow hb1 hrd0.le (show rd ≤ b ^ (1 : ℝ) by rw [Real.rpow_one]; exact hrd) _
      (by push_cast; rw [hM]; linarith [mul_le_mul_of_nonneg_right (hRR.trans h25) hF0])
  have hTTb : TT ^ (6 * f) ≤ Real.exp (12 * CT * M * Real.log b) :=
    hpow hb1 hTT0.le hTT _
      (by push_cast; rw [hM]; linarith [mul_nonneg (mul_nonneg hCT (sub_nonneg.2 h15)) hF0])
  have hgA : (g ^ f) ^ (A * (r + 1) ^ 2) ≤ Real.exp (Cg * A * M * Real.log b) := by
    rw [← pow_mul]
    exact hpow hb1 hg0 hg _ (by
      push_cast; rw [hM]
      linarith [mul_nonneg (mul_nonneg (mul_nonneg hCg (Nat.cast_nonneg A))
        (sub_nonneg.2 (hR2.trans h25))) hF0])
  have hrd2 : (rd / 2) ^ (f * (r + 1)) ≤ Real.exp (1 * M * Real.log b) :=
    hpow hb1 (div_nonneg hrd0.le (by norm_num)) (show rd / 2 ≤ b ^ (1 : ℝ) by rw [Real.rpow_one]; linarith) _
      (by push_cast; rw [hM]; linarith [mul_le_mul_of_nonneg_right (hRm.trans h15) hF0])
  have hgg : g ^ (f * (r + 1) * (2 * r + 3)) ≤ Real.exp (Cg * M * Real.log b) :=
    hpow hb1 hg0 hg _
      (by push_cast; rw [hM]; linarith [mul_nonneg (mul_nonneg hCg (sub_nonneg.2 (hR3.trans h25))) hF0])
  have hp1 := mul_le_mul hcS he1 he0 (Real.exp_pos _).le
  have hp2 := mul_le_mul hrdb hTTb (pow_nonneg hTT0.le _) (Real.exp_pos _).le
  have hp3 := mul_le_mul hp1 hp2 (mul_nonneg (pow_nonneg hrd0.le _) (pow_nonneg hTT0.le _)) (by positivity)
  have hp4 := mul_le_mul hp3 hgA (pow_nonneg (pow_nonneg hg0 _) _) (by positivity)
  have hp5 := mul_le_mul_of_nonneg_right hp4 (Real.exp_pos (CB * M * Real.log b)).le
  have hp6 := mul_le_mul h64 hp5
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 he0)
      (mul_nonneg (pow_nonneg hrd0.le _) (pow_nonneg hTT0.le _))) (pow_nonneg (pow_nonneg hg0 _) _))
      (Real.exp_pos _).le) (Real.exp_pos _).le
  have hp7 := mul_le_mul hrd2 hgg (pow_nonneg hg0 _) (Real.exp_pos _).le
  have hp8 := mul_le_mul hp6 hp7
    (mul_nonneg (pow_nonneg (div_nonneg hrd0.le (by norm_num)) _) (pow_nonneg hg0 _)) (by positivity)
  refine hp8.trans (le_of_eq ?_)
  simp only [← Real.exp_add]
  congr 1
  ring
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
