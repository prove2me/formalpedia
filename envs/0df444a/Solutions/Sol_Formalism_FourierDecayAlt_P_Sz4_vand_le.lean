-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.vand_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:27.774736+00:00
-- url     : https://prove2.me/submissions/531ae278-909b-43a3-a28d-c97c8601cb4d

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_vandermondeNonTop
import Theorems.Thm_Formalism_FourierDecayAlt_P_vandermondeTop
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_a_sub_u_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_kDel_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_edge_ratio_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_bp_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_top_ratio_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_a_sub_ulast_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_u_decomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_top_decomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_combine
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_le_of_ratio
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vthp_small

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (hv : c.vth ≤ 1 / 10) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') :
    0 < Vand c.k (c.u de) ∧
      Vand c.k (c.u de') ≤ Real.exp ((c.k : ℝ) / 2 + 1) * Vand c.k (c.u de) := by
  have hkD := kDel_pos c hc
  have hC := a_sub_ulast_pos c hc
  have hEpos : ∀ d : ℕ → ℝ, IsWord c.k d → ∀ i ∈ Icc 2 (c.k - 1), 0 < c.a - c.u d i := by
    intro d hd i hi
    have := a_sub_u_pos c d hc hd i hi; linarith
  have hE := Finset.prod_pos (hEpos de hw)
  have hE' := Finset.prod_pos (hEpos de' hw')
  have hEE := prod_le_of_ratio _ _ _ _ (hEpos de hw) (edge_ratio_le c de' de hc hw' hw)
  rw [vand_u_decomp c de hc, vand_u_decomp c de' hc]
  by_cases ht : c.top = true
  · obtain ⟨hW, hR, hR1, _, _⟩ := vandermondeTop c de hc hw
    obtain ⟨_, hR', _, hR2', _⟩ := vandermondeTop c de' hc hw'
    have hb := bp_pos c hc ht
    have hFpos : ∀ d : ℕ → ℝ, IsWord c.k d → ∀ i ∈ Icc 2 (c.k - 1), 0 < c.u d i + c.bp := by
      intro d hd i hi
      have := u_mid_nonneg c d hc hd i hi; linarith
    have hF := Finset.prod_pos (hFpos de hw)
    have hF' := Finset.prod_pos (hFpos de' hw')
    have hFF := prod_le_of_ratio _ _ _ _ (hFpos de hw) (top_ratio_le c de' de hc ht hw' hw)
    have hvp := vthp_small c hc hv ht
    rw [vand_top_decomp c de hc ht, vand_top_decomp c de' hc ht, hR, hR']
    have hRpos : 0 < Rde (c.k - 2) de := lt_of_lt_of_le (Real.exp_pos _) hR1
    refine ⟨by positivity, ?_⟩
    have key := combine
      ((∏ j ∈ Icc 2 (c.k - 1), (c.a - c.u de j)) * ∏ i ∈ Icc 2 (c.k - 1), (c.u de i + c.bp))
      ((∏ j ∈ Icc 2 (c.k - 1), (c.a - c.u de' j)) * ∏ i ∈ Icc 2 (c.k - 1), (c.u de' i + c.bp))
      (c.a - c.ulast) (Rde (c.k - 2) de) (Rde (c.k - 2) de') (Vand (c.k - 2) c.v)
      (Real.exp (1 / 3) * Real.exp (c.vthp / 3)) (Real.exp (((c.k : ℝ) - 1) / 4))
      (Real.exp (-(((c.k : ℝ) - 1) / 4))) (Real.exp ((c.k : ℝ) / 2 + 1))
      (mul_pos hE hF) (mul_pos hE' hF') hC hW (Real.exp_pos _) (Real.exp_pos _)
      (by
        calc _ ≤ (Real.exp (1 / 3) * ∏ j ∈ Icc 2 (c.k - 1), (c.a - c.u de j)) *
              (Real.exp (c.vthp / 3) * ∏ i ∈ Icc 2 (c.k - 1), (c.u de i + c.bp)) :=
              mul_le_mul hEE hFF hF'.le (by positivity)
          _ = _ := by ring)
      hR2' hR1
      (by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith)
    calc _ = _ := by ring
      _ ≤ _ := key
      _ = _ := by ring
  · have ht' : c.top = false := by simpa using ht
    obtain ⟨hW, hR, hR1, _⟩ := vandermondeNonTop c de hc hw ht'
    obtain ⟨_, hR', _, hR2'⟩ := vandermondeNonTop c de' hc hw' ht'
    rw [hR, hR']
    have hRpos : 0 < Rde (c.k - 1) de := lt_of_lt_of_le (Real.exp_pos _) hR1
    refine ⟨by positivity, ?_⟩
    exact combine _ _ _ _ _ _ (Real.exp (1 / 3)) (Real.exp ((c.k : ℝ) / 4))
      (Real.exp (-((c.k : ℝ) / 4))) (Real.exp ((c.k : ℝ) / 2 + 1)) hE hE' hC hW (Real.exp_pos _)
      (Real.exp_pos _) hEE hR2' hR1
      (by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith)
end Formalism.FourierDecayAlt.P.Sz4
