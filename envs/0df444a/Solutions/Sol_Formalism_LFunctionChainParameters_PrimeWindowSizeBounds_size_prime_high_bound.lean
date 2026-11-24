-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_prime_high_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:38.765809+00:00
-- url     : https://prove2.me/submissions/90170949-1982-47ee-a14d-03d1dd79761a

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_le_three_halves
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_x1__a3dada
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Epos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Spos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Xpos__19fb6e
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_sb1
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_hbsb
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpow_le
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kzr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kzr0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_div_le_div_sq_of_le
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_npos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_sg0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_r_sg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_close_sg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_br_sg
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyXS__85083eb7ab8a
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyX__ac9c7cc18615
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_xprime_q_two_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : SizePrHigh := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tPrHigh unitU
  have h1 := F.C0; have h2 := F.CK; have h9 := F.xpos; have h10 := F.Xpos; have h11 := F.Kpos
  have h12 := F.Epos; have h13 := F.Spos; have hb := F.b0; have hz := F.zpos
  have hlx0 := F.lx0; have hlx := F.lxz; have hw0 : 0 ≤ w8 := by linarith [F.w81]
  have hw := F.w8z
  have hr0 := F.rpos
  have p2 : 4 * (P.C * X * (P.η + P.Sc)) ≤ sg P K * P.b := by
    have a1 := F.η0; have a2 := F.ηS; have a3 := F.Sc0; have a4 := F.ScS
    have a5 : 8 * K * (E ^ 0 * P.x ^ 0) * (X * S) ≤ sg P K * P.b :=
      F.polyXS' (by norm_num) (by norm_num) (by norm_num)
    have a6 : P.C * X * (P.η + P.Sc) ≤ K * X * (S + S) := by gcongr
    have a7 : 4 * (K * X * (S + S)) = 8 * K * (E ^ 0 * P.x ^ 0) * (X * S) := by ring
    linarith
  have p3 : 4 * (P.C * (P.b / P.n) * P.lx * w8) ≤ sg P K * P.b := by
    have a1 : P.b / P.n ≤ P.b * P.x⁻¹ ^ 2 := F.div_le_div_sq_of_le (le_refl _) hb F.nx
    have a0 : 0 ≤ P.b / P.n := div_nonneg hb F.npos.le
    have a2 : P.C * (P.b / P.n) * P.lx * w8 ≤ K * (P.b * P.x⁻¹ ^ 2) * z * z := by gcongr
    have a3 : 4 * (K * (P.b * P.x⁻¹ ^ 2) * z * z)
        = P.b * (4 / 100 * (100 * K * z ^ 2 * P.x⁻¹)) * P.x⁻¹ := by ring
    have b1 := F.Kzr (i := 2) (by norm_num)
    have b0 := F.Kzr0 2
    have a4 : P.b * (4 / 100 * (100 * K * z ^ 2 * P.x⁻¹)) * P.x⁻¹ ≤ sg P K * P.b :=
      F.close_sg (by linarith) (by linarith) hr0.le F.r_sg
    linarith
  have p4 : 4 * (P.C * X * P.t * P.lx * w8) ≤ sg P K * P.b := by
    have a1 := F.t0; have a2 := F.tE
    have a3 : z * z ≤ P.x := by
      have := F.zpow_le (i := 2) (by norm_num)
      have b1 : 1 * z ^ 2 ≤ 100 * K * z ^ 2 := by
        have : (1 : ℝ) ≤ 100 * K := by linarith [F.hK]
        gcongr
      nlinarith
    have a4 : P.C * X * P.t * P.lx * w8 ≤ K * X * E * z * z := by gcongr
    have a5 : K * X * E * z * z ≤ K * X * E * P.x := by
      have : K * X * E * z * z = K * X * E * (z * z) := by ring
      rw [this]; gcongr
    have a6 : 4 * K * (E ^ 1 * P.x ^ 1) * X ≤ sg P K * P.b :=
      F.polyX' (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have a7 : 4 * (K * X * E * P.x) = 4 * K * (E ^ 1 * P.x ^ 1) * X := by ring
    linarith
  have p5 : 4 * (X * P.bo) ≤ sg P K * P.b := by
    have a1 := F.bo0; have a2 := F.bosb; have a3 := F.hbsb; have a4 := F.sb1
    have a5 : X * P.bo ≤ X * sb := by gcongr
    have a6 : 4 * 1 * (1 * P.x) * (X * 1) * sb ≤ 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) * sb := by
      have c1 := F.hK; have c2 := F.S1
      have c3 : 1 ≤ E ^ 4 := one_le_pow₀ F.E1
      have c4 : P.x ≤ P.x ^ 4 := by
        calc P.x = P.x ^ 1 := (pow_one _).symm
          _ ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
      gcongr
      norm_num
    have a7 : 4 * (X * sb) = (4 * 1 * (1 * P.x) * (X * 1) * sb) * P.x⁻¹ := by
      have : (4 * 1 * (1 * P.x) * (X * 1) * sb) * P.x⁻¹ = 4 * (X * sb) * (P.x * P.x⁻¹) := by ring
      rw [this, F.xr, mul_one]
    have a8 : (4 * 1 * (1 * P.x) * (X * 1) * sb) * P.x⁻¹ ≤ P.b * P.x⁻¹ :=
      mul_le_mul_of_nonneg_right (a6.trans a3) hr0.le
    have a9 := F.br_sg
    linarith
  have hXQ : P.Xp * P.Q₂ ≤ (P.C + sg P K) * P.b := by
    rw [xprime_q_two_expand F]; linarith
  have hsb0 : 0 ≤ sg P K * P.b := mul_nonneg F.sg0 hb
  have key : 2 * Real.log 4 * (P.Xp * P.Q₂) ≤ (2 * Real.log 4 * P.C + 3 * sg P K) * P.b := by
    have a1 : 2 * Real.log 4 * (P.Xp * P.Q₂) ≤ 2 * Real.log 4 * ((P.C + sg P K) * P.b) :=
      mul_le_mul_of_nonneg_left hXQ (by linarith [log_four_nonneg])
    have a2 : 2 * Real.log 4 * (sg P K * P.b) ≤ 3 * (sg P K * P.b) :=
      mul_le_mul_of_nonneg_right (by linarith [log_four_le_three_halves]) hsb0
    linarith
  exact scale2 hm hT key
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
