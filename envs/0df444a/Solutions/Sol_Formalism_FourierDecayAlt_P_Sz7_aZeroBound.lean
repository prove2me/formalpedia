-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz7.aZeroBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:33.612058+00:00
-- url     : https://prove2.me/submissions/d3846c14-695a-488c-b572-7ca713ca991e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz
private lemma vthp_nonneg_of_ok (c : Cfg) (h : c.Ok) : 0 ≤ c.vthp := by
  unfold Cfg.vthp
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith)) hbp.le
  · exact le_refl _
private lemma vthp_le_one_tenth_of_small (c : Cfg) (h : c.Ok) (bb : ℝ) (hs : c.Small bb) : c.vthp ≤ 1 / 10 := by
  unfold Cfg.vthp
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hm : (2:ℝ) ≤ c.m := by exact_mod_cast h.hm
    have hk : (0:ℝ) ≤ c.k := Nat.cast_nonneg _
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    have hv := hs.hvth
    unfold Cfg.vth at hv
    rw [div_le_iff₀ (by linarith)] at hv
    rw [div_le_iff₀ hbp]
    have hkD : 0 ≤ (c.k:ℝ) * c.Del := mul_nonneg hk (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hm hkD]
  · norm_num
end Formalism.FourierDecayAlt.P.Sz7
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz7
theorem _root_.solution : AZeroBound := by
  intro c bb h hs
  have hv0 := vthp_nonneg_of_ok c h
  have hv1 := vthp_le_one_tenth_of_small c h bb hs
  have hW : 0 < 1 + c.vthp := by linarith
  have hE2 : (9:ℝ) / 10 ≤ Real.exp (-(2 * c.m * Real.log bb / c.k)) := by
    have := Real.add_one_le_exp (-(2 * c.m * Real.log bb / c.k))
    linarith [hs.hmu]
  have hE1 : Real.exp c.vth ≤ 10 / 9 := by
    have h1 := Real.add_one_le_exp (-c.vth)
    have h2 : Real.exp c.vth * Real.exp (-c.vth) = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos c.vth
    have h4 := hs.hvth
    nlinarith [mul_le_mul_of_nonneg_left h1 h3.le, mul_nonneg h3.le (by linarith : (0:ℝ) ≤ 1 / 10 - c.vth)]
  have hS : Real.sqrt (14 / 5) ≤ 1.6734 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 14 / 5 by norm_num), Real.sqrt_nonneg (14 / 5)]
  have hSE : Real.sqrt (14 / 5) * Real.exp c.vth ≤ 1.6734 * (10 / 9) :=
    mul_le_mul hS hE1 (Real.exp_pos _).le (by norm_num)
  have hcOne : 0 < cOne c bb := by
    unfold cOne
    exact div_pos (by positivity) hW
  have hcLow : 0.38 * (9 / 10) / (11 / 10) ≤ cOne c bb := by
    unfold cOne
    rw [le_div_iff₀ hW]
    have : 0.38 * (9 / 10) / (11 / 10) * (1 + c.vthp) ≤ 0.38 * (9 / 10) := by
      have : (1 + c.vthp) ≤ 11 / 10 := by linarith
      nlinarith
    linarith
  refine ⟨?_, ?_⟩
  · unfold AZero
    exact div_pos (by positivity) hcOne
  · unfold AZero
    rw [div_le_iff₀ hcOne]
    nlinarith [hSE, hcLow]
end Formalism.FourierDecayAlt.P.Sz7
