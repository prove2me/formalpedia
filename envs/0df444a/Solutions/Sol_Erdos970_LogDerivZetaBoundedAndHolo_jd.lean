-- Prove2me | solution 1 for Erdos970.LogDerivZetaBoundedAndHolo_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:20:28.394902+00:00
-- url     : https://prove2.me/submissions/3c96842e-0eb5-41c5-8a45-3d8dff980f26

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT3_RiemannZeta
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open scoped BigOperators Topology

open _root_.Real _root_.Set _root_.Filter Topology _root_.MeasureTheory
open scoped BigOperators Topology

open Metric _root_.Set _root_.Filter Asymptotics BigOperators

lemma Zeta1_Zeta_Expand :
    ∃ A > 1, ∃ b > 1,
    ∀ (t : ℝ) (_ht : |t| > 2)
    (r1 r R1 R : ℝ)
    (_hr1_pos : 0 < r1) (_hr1_lt_r : r1 < r)
    (_hr_pos : 0 < r) (_hr_lt_R1 : r < R1) (_hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc R1 c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc R1 c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
      (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * (Real.log |t| + Real.log b + A) := by
                                                           
  obtain ⟨b, hbgt1, hb⟩ := zeta32upper
  obtain ⟨A, hAgt1, hA⟩ := zeta32lower_log

  refine ⟨A, hAgt1, b, hbgt1, ?_⟩
  intro t ht r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 c hfin z hz

  have hexp_lemma := log_Deriv_Expansion_Zeta t ht r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1

  have htpos : (0 : ℝ) < |t| := by linarith [ht]
  have hBgt1 : b * |t| > 1 := by
    have hb_pos : (0 : ℝ) < b := by linarith [hbgt1]
    calc (1 : ℝ) < 1 * 2 := by norm_num
    _ < b * 2 := mul_lt_mul_of_pos_right (by linarith [hbgt1]) (by norm_num)
    _ < b * |t| := mul_lt_mul_of_pos_left ht hb_pos

  have hbound_ball : ∀ s ∈ closedBall (3/2 + I * t) R, ‖riemannZeta s‖ < b * |t| := by
    have hsubset : closedBall (3/2 + I * t) R ⊆ closedBall (3/2 + I * t) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1)
    intro s hs
    have hs1 : s ∈ closedBall (3/2 + I * t) 1 := hsubset hs
    have ht2 : |t| > 2 := by linarith [ht]
    specialize hb t ht2
    exact hb s hs1

  have hexp := hexp_lemma (b * |t|) hBgt1 hbound_ball hfin z hz

  have hζne : riemannZeta (3/2 + I * t) ≠ 0 := zetacnot0 t
  have hζpos : (0 : ℝ) < ‖riemannZeta (3/2 + I * t)‖ := norm_pos_iff.mpr hζne

  have hBpos : (0 : ℝ) < b * |t| := mul_pos (by linarith [hbgt1]) htpos
  have hBne : b * |t| ≠ 0 := ne_of_gt hBpos
  have htne : |t| ≠ 0 := ne_of_gt htpos
  have hbne : b ≠ 0 := ne_of_gt (by linarith [hbgt1])

  have hlog_bound : Real.log (b * |t| / ‖riemannZeta (3/2 + I * t)‖) ≤
                    Real.log |t| + Real.log b + A := by
    rw [Real.log_div hBne (ne_of_gt hζpos)]
    rw [Real.log_mul hbne htne]
                                  
    have hA_bound := hA t
    have : -Real.log ‖riemannZeta (3/2 + I * t)‖ ≤ A := by
      have eq_neg : Real.log (1 / ‖riemannZeta (3/2 + I * t)‖) = -Real.log ‖riemannZeta (3/2 + I * t)‖ := by
        rw [Real.log_div (by norm_num) (ne_of_gt hζpos)]
        simp
      rw [← eq_neg]
      exact hA_bound
    linarith

  have hcoeff_nonneg : (0 : ℝ) ≤ 16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) := by
    apply add_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · apply sq_nonneg
      · apply le_of_lt
        apply pow_pos
        linarith [hr1_lt_r]
    · apply div_nonneg
      · norm_num
      · apply le_of_lt
        apply mul_pos
        ·                          
          have h_gt : R > R1 := hR1_lt_R
          have h1_pos : (1 : ℝ) < R/R1 := by
            rw [one_lt_div]
            · exact h_gt
            · exact hR1_pos
          have h_sq_div : R^2/R1 = R * (R/R1) := by
            field_simp [ne_of_gt hR1_pos]
          rw [h_sq_div]
          have h_r_pos : (0 : ℝ) < R := by linarith [hR1_pos, h_gt]
          have : R * (R/R1) > R * 1 := by
            apply mul_lt_mul_of_pos_left h1_pos h_r_pos
          simp at this
          linarith [this]
        · apply Real.log_pos
          rw [one_lt_div]
          · exact hR1_lt_R
          · exact hR1_pos

  calc ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
      ≤ (16 * r^2 / ((r - r1)^3) +
          1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (b * |t| / ‖riemannZeta (3/2 + I * t)‖) := hexp
    _ ≤ (16 * r^2 / ((r - r1)^3) +
          1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * (Real.log |t| + Real.log b + A) := by
      exact mul_le_mul_of_nonneg_left hlog_bound hcoeff_nonneg

lemma Zeta1_Zeta_Expansion
    (r1 r : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < 5 / (6 : ℝ)) :
    ∃ C > 1,
    ∀ (t : ℝ) (_ht : |t| > 3),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc (5 / (6 : ℝ)) c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
      C * (1 / (r - r1)^3 + 1) * Real.log |t| := by
                                                             
  obtain ⟨A, hAgt1, b, hbgt1, hmain⟩ := Zeta1_Zeta_Expand
                      
  let R1 : ℝ := 5 / 6
  let R  : ℝ := 8 / 9
  have hR1_pos : 0 < R1 := by norm_num [R1]
  have hR1_lt_R : R1 < R := by norm_num [R1, R]
  have hR_lt_1  : R < 1 := by norm_num [R]
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
                                    
  let d : ℝ := (r - r1) ^ 3
  have hd_pos : 0 < d := by
    have : 0 < r - r1 := sub_pos.mpr hr1_lt_r
    simpa [d] using pow_pos this 3
  let A0 : ℝ := 1 / ((R^2 / R1 - R1) * Real.log (R / R1))
  have hA0_pos : 0 < A0 := by
    have hx1 : 0 < R^2 / R1 - R1 := by
                                              
      norm_num [R, R1]
    have hx2 : 0 < Real.log (R / R1) := by
                         
      have : (1 : ℝ) < R / R1 := by norm_num [R, R1]
      exact Real.log_pos this
    have hxden : 0 < (R^2 / R1 - R1) * Real.log (R / R1) := mul_pos hx1 hx2
    simpa [A0] using (one_div_pos.mpr hxden)
                                                               
  let K : ℝ := 16 * r^2 / d + A0
                              
  let S : ℝ := Real.log b + A
  have hS_pos : 0 < S := by
    have hbpos : 0 < Real.log b := Real.log_pos hbgt1
    have hApos : 0 < A := lt_trans (by norm_num) hAgt1
    exact add_pos hbpos hApos
                                                                                          
  let Kcoeff : ℝ := max (16 * r^2) A0
  have hK_le : K ≤ Kcoeff * (1 / d + 1) := by
    have hx_nonneg : 0 ≤ 1 / d := by
      exact le_of_lt (one_div_pos.mpr hd_pos)
    have hα_le : 16 * r^2 / d ≤ Kcoeff * (1 / d) := by
        have hα : 16 * r^2 ≤ Kcoeff := le_max_left _ _
        have : (16 * r^2) * (1 / d) ≤ Kcoeff * (1 / d) :=
          mul_le_mul_of_nonneg_right hα hx_nonneg
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hβ_le : A0 ≤ Kcoeff * 1 := by
      have hβ : A0 ≤ Kcoeff := le_max_right _ _
      simpa using hβ
    have : 16 * r^2 / d + A0 ≤ Kcoeff * (1 / d) + Kcoeff * 1 :=
      add_le_add hα_le hβ_le
    simpa [K, mul_add, mul_one, add_comm, add_left_comm, add_assoc] using this
                                                  
  let C : ℝ := max (Kcoeff * (1 + S / Real.log 3)) 2
  have hC_gt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hC_gt1, ?_⟩
                                                          
  intro t ht
                                         
  simp only
  intro hfin z hz
                                                
  have ht2 : |t| > 2 := by linarith [ht]
  have hineq0 :=
    hmain t ht2 r1 r R1 R hr1_pos hr1_lt_r (lt_trans hr1_pos hr1_lt_r) hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1
  have hineq1 := hineq0 hfin z hz
                                 
  have hK_eq : (16 * r^2 / (r - r1)^3 + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) = K := by
    simp [K, A0, d, R1, R]
  have hLS_eq : Real.log |t| + Real.log b + A = Real.log |t| + S := by
    simp [S, add_comm, add_assoc]
  have hineq2 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ K * (Real.log |t| + S) := by
    rw [← hK_eq, ← hLS_eq]
    exact hineq1
                                                             
  have hlog3pos : 0 < Real.log (3 : ℝ) := by
    have : (1 : ℝ) < 3 := by norm_num
    exact Real.log_pos this
                                           
  have hpos_t : 0 < |t| := lt_trans (by norm_num) ht
  have hL_ge_log3' : Real.log 3 ≤ Real.log |t| := by
    have hge : (3 : ℝ) ≤ |t| := le_of_lt ht
    exact Real.log_le_log (by norm_num) hge
  have hratio_nonneg : 0 ≤ S / Real.log 3 := le_of_lt (div_pos hS_pos hlog3pos)
  have hneq : Real.log 3 ≠ 0 := ne_of_gt hlog3pos

  have hS_le : S ≤ (S / Real.log 3) * Real.log |t| := by

    calc S
      = (S / Real.log 3) * Real.log 3 := by simp [hneq]
      _ ≤ (S / Real.log 3) * Real.log |t| := mul_le_mul_of_nonneg_left hL_ge_log3' hratio_nonneg

  have hsum_bound : Real.log |t| + S ≤ (1 + S / Real.log 3) * Real.log |t| := by
    have hstep : Real.log |t| + S ≤ Real.log |t| + (S / Real.log 3) * Real.log |t| :=
      add_le_add_right hS_le (Real.log |t|)
                                                                                           
    have h_factor : Real.log |t| + (S / Real.log 3) * Real.log |t| = (1 + S / Real.log 3) * Real.log |t| := by ring
    rw [← h_factor]
    exact hstep
                                      
  have hineq3 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ K * ((1 + S / Real.log 3) * Real.log |t|) :=
    le_trans hineq2 (mul_le_mul_of_nonneg_left hsum_bound (by
      have hr2_nonneg : 0 ≤ r^2 := by
        have : 0 ≤ r * r := mul_nonneg (le_of_lt hr_pos) (le_of_lt hr_pos)
        simpa [pow_two] using this
      have hterm1 : 0 ≤ 16 * r^2 / d :=
        div_nonneg (mul_nonneg (by norm_num) hr2_nonneg) (le_of_lt hd_pos)
      have : 0 ≤ K := add_nonneg hterm1 (le_of_lt hA0_pos)
      exact this))
                                    
  have hKcoeff : K * ((1 + S / Real.log 3) * Real.log |t|)
      ≤ (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 3) * Real.log |t|) :=
    mul_le_mul_of_nonneg_right hK_le (by
      have hLpos : 0 < Real.log |t| :=
        Real.log_pos (lt_trans (by norm_num) ht)
      have hcoef_pos : 0 < 1 + S / Real.log 3 :=
        add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt (div_pos hS_pos hlog3pos))
      have : 0 ≤ (1 + S / Real.log 3) * Real.log |t| :=
        le_of_lt (mul_pos hcoef_pos hLpos)
      simpa using this)
                                                                     
  have hfinal := le_trans hineq3 hKcoeff
                                                    
  have hC_ge : Kcoeff * (1 + S / Real.log 3) ≤ C := by
    exact le_max_left _ _
                                           
  have : (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 3) * Real.log |t|)
      ≤ C * (1 / d + 1) * Real.log |t| := by
    have hnonneg_term : 0 ≤ (1 / d + 1) * Real.log |t| := by
      have h1 : 0 ≤ 1 / d := le_of_lt (one_div_pos.mpr hd_pos)
      have h2 : 0 ≤ Real.log |t| := le_of_lt (Real.log_pos (lt_trans (by norm_num) ht))
      have : 0 ≤ (1 / d + 1) := add_nonneg h1 (by norm_num)
      exact mul_nonneg this h2
    have hstep := mul_le_mul_of_nonneg_left hC_ge hnonneg_term
                                         
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
                                                    
  have hfinal_le := le_trans hfinal this
  simp only [d] at hfinal_le
  exact hfinal_le

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_ZetaBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open _root_.Complex Topology _root_.Filter Interval _root_.Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz

theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt

lemma LogDerivZetaHoloOn {S : Set ℂ} (s_ne_one : 1 ∉ S)
    (nonzero : ∀ s ∈ S, ζ s ≠ 0) :
    HolomorphicOn (fun s ↦ ζ' s / ζ s) S := by
  apply DifferentiableOn.div _ _ nonzero <;> intro s hs <;> apply DifferentiableAt.differentiableWithinAt
  · apply differentiableAt_deriv_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one
  · apply differentiableAt_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one

open _root_.ArithmeticFunction (vonMangoldt)

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT4_ZeroFreeRegion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


lemma zerofree_constant_pos : 0 < zerofree_constant :=
  (Classical.choose_spec zerofree).1

lemma zerofree_constant_lt_one : zerofree_constant < 1 :=
  (Classical.choose_spec zerofree).2.1

lemma lem_delta19 :
  (∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9)) ∧
  (∀ t : ℝ, |t| > 2 → (0 < deltaz_t t ∧ deltaz_t t < 1/9)) := by
                                          
  have h_complex : ∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9) := by
    intro z hz
    constructor
    ·                     
      have h_num_pos : 0 < zerofree_constant / 20 := by
        exact div_pos zerofree_constant_pos (by norm_num)
      have h_den_pos : 0 < Real.log (|z.im| + 2) := by
        have h_gt_one : (1 : ℝ) < |z.im| + 2 := by
          have h_nonneg : (0 : ℝ) ≤ |z.im| := abs_nonneg _
          linarith [hz]
        exact Real.log_pos h_gt_one
      unfold deltaz
      exact div_pos h_num_pos h_den_pos
    ·                       
                                       
      have h_den_ge_half : (1/2 : ℝ) ≤ Real.log (|z.im| + 2) := by
                                         
        have h_den_ge_log2 : Real.log 2 ≤ Real.log (|z.im| + 2) := by
          have h_pos : 0 < |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          have h_le : (2 : ℝ) ≤ |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          exact Real.log_le_log (by norm_num) h_le
                                              
        have h_log2_ge_half : (1/2 : ℝ) ≤ Real.log 2 := by
          have h_exp_half_le_two : Real.exp (1/2) ≤ 2 := by
                                                                 
            have h_exp_one_lt_three : Real.exp 1 < 3 := lem_three_gt_e
            have h_exp_sq : (Real.exp (1/2))^2 = Real.exp 1 := by
              rw [pow_two, ← Real.exp_add]; norm_num
            have h_exp_sq_lt_four : (Real.exp (1/2))^2 < 4 := by
              rw [h_exp_sq]; linarith [h_exp_one_lt_three]
                                               
            have h_exp_pos : 0 ≤ Real.exp (1/2) := le_of_lt (Real.exp_pos _)
            have h_two_pos : 0 ≤ (2 : ℝ) := by norm_num
            have h_four_eq : (2 : ℝ)^2 = 4 := by norm_num
            rw [← h_four_eq] at h_exp_sq_lt_four
            have h_lt_abs := (sq_lt_sq).mp h_exp_sq_lt_four
            rw [abs_of_nonneg h_exp_pos, abs_of_nonneg h_two_pos] at h_lt_abs
            exact le_of_lt h_lt_abs
          exact (Real.le_log_iff_exp_le (by norm_num : 0 < (2 : ℝ))).mpr h_exp_half_le_two
        exact le_trans h_log2_ge_half h_den_ge_log2
                                            
      have h_inv_le_two : 1 / Real.log (|z.im| + 2) ≤ 2 := by
        have h_pos_half : 0 < (1/2 : ℝ) := by norm_num
        have h_ineq := one_div_le_one_div_of_le h_pos_half h_den_ge_half
        convert (preTransparency := .instances) h_ineq using 1 <;> first | rfl | norm_num
                           
      have h_bound : deltaz z ≤ zerofree_constant / 10 := by
        unfold deltaz

        rw [div_eq_mul_inv]
                                                                                              
        have h_num_nonneg : 0 ≤ zerofree_constant / 20 := by
          exact le_of_lt (div_pos zerofree_constant_pos (by norm_num))
        have h_mul_ineq := mul_le_mul_of_nonneg_left h_inv_le_two h_num_nonneg
        convert (preTransparency := .instances) h_mul_ineq using 1 <;> first | rfl | ring
                                                         
      have h_lt_tenth : zerofree_constant / 10 < 1 / 10 := by
        exact div_lt_div_of_pos_right zerofree_constant_lt_one (by norm_num)
      have h_tenth_lt_ninth : (1 : ℝ) / 10 < 1 / 9 := by norm_num
      exact lt_trans (lt_of_le_of_lt h_bound h_lt_tenth) h_tenth_lt_ninth

  constructor
  · exact h_complex
  ·              
    intro t ht
                                                                             
    have h_eq : deltaz_t t = deltaz (t * Complex.I) := rfl
    rw [h_eq]
    have h_im_eq : |(t * Complex.I).im| = |t| := by simp
    rw [← h_im_eq] at ht
    exact h_complex (t * Complex.I) ht

lemma closedBall_compact_complex (c : ℂ) (r : ℝ) :
    IsCompact (Metric.closedBall c r) := by
                                                                           
  exact ProperSpace.isCompact_closedBall c r

lemma riemannZeta_no_zeros_accumulate_at_one :
  ∀ Z : Set ℂ, (∀ z ∈ Z, riemannZeta z = 0) → ¬AccPt 1 (Filter.principal Z) := by
  intro Z hZ
                           
  by_contra h_acc

  have h_residue := riemannZeta_residue_one

  rw [Metric.tendsto_nhdsWithin_nhds] at h_residue
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := h_residue (1/2) (by norm_num : (0 : ℝ) < 1/2)

  rw [accPt_iff_nhds] at h_acc

  obtain ⟨y, ⟨hy_ball, hy_Z⟩, hy_ne⟩ := h_acc (Metric.ball 1 δ) (Metric.ball_mem_nhds 1 hδ_pos)

  have hy_zero : riemannZeta y = 0 := hZ y hy_Z

  have hy_in_compl : y ∈ ({1} : Set ℂ)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hy_ne

  have hy_dist : dist y 1 < δ := hy_ball

  have h_bound := hδ_bound hy_in_compl hy_dist

  rw [hy_zero, mul_zero] at h_bound

  have h_dist_eq : dist (0 : ℂ) (1 : ℂ) = 1 := by
    rw [Complex.dist_eq]
    norm_num

  rw [h_dist_eq] at h_bound
                                                 
  norm_num at h_bound

lemma complex_minus_singleton_connected : IsPreconnected ({s : ℂ | s ≠ 1} : Set ℂ) := by
                                                                   
  have h_eq : {s : ℂ | s ≠ 1} = ({1} : Set ℂ)ᶜ := by
    ext x
    simp [Set.mem_compl_iff, Set.mem_singleton_iff]

  rw [h_eq]

  have h_rank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
                                         
    norm_num

  have h_connected := isConnected_compl_singleton_of_one_lt_rank h_rank (1 : ℂ)

  exact h_connected.isPreconnected

lemma eventually_eq_zero_implies_frequently_eq_zero_punctured (f : ℂ → ℂ) (z₀ : ℂ) :
  (∀ᶠ z in nhds z₀, f z = 0) → (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0) := by
  intro h_eventually

  have h_nebot : Filter.NeBot (nhdsWithin z₀ {z₀}ᶜ) := by
                                                                                
    exact NormedField.nhdsNE_neBot z₀

  have h_eventually_punctured : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0 := by
                                                        
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds h_eventually

  exact h_eventually_punctured.frequently

lemma riemannZeta_zeros_finite_of_compact (K : Set ℂ) (hK : IsCompact K) :
    {z ∈ K | riemannZeta z = 0}.Finite := by

  by_contra h_not_finite
  push Not at h_not_finite

  let Z := {z ∈ K | riemannZeta z = 0}

  have hZ_inf : Z.Infinite := h_not_finite
  have hZ_sub : Z ⊆ K := fun z hz => hz.1

  obtain ⟨z₀, hz₀_K, hz₀_acc⟩ := lem_bolzano_weierstrass hK hZ_inf hZ_sub

  by_cases h_eq_one : z₀ = 1
  ·                                                               
    subst h_eq_one
                                                 
    have hZ_zeros : ∀ z ∈ Z, riemannZeta z = 0 := fun z hz => hz.2
                                                              
    exact riemannZeta_no_zeros_accumulate_at_one Z hZ_zeros hz₀_acc

  ·                                    
                                                                 
    have h_analytic : AnalyticAt ℂ riemannZeta z₀ :=
      zetaanalOnnot1 z₀ h_eq_one

    obtain h_ev_zero | h_ev_ne := h_analytic.eventually_eq_zero_or_eventually_ne_zero

    ·                                                                

      have h_freq := eventually_eq_zero_implies_frequently_eq_zero_punctured riemannZeta z₀ h_ev_zero

      have h_eq_on_zero := zetaanalOnnot1.eqOn_zero_of_preconnected_of_frequently_eq_zero
        complex_minus_singleton_connected h_eq_one h_freq

      have : riemannZeta 0 = 0 := h_eq_on_zero (by simp : (0 : ℂ) ∈ {s | s ≠ 1})
      rw [riemannZeta_zero] at this
      norm_num at this

    ·                                                                       

      unfold AccPt at hz₀_acc

      have h_ev_not_Z : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, z ∉ Z := by
        apply Filter.Eventually.mono h_ev_ne
        intro z hz hz_in_Z
        exact hz hz_in_Z.2

      have h_ev_false : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z, False := by
        rw [Filter.eventually_inf_principal]
        exact h_ev_not_Z

      have h_eq_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z = ⊥ :=
        Filter.eventually_false_iff_eq_bot.mp h_ev_false

      have h_ne_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z ≠ ⊥ := hz₀_acc.ne

      exact h_ne_bot h_eq_bot

lemma lem_ZFRdelta :
  ∀ z : ℂ, 2 < |z.im| → z.re > 1 - 9 * deltaz z → riemannZeta z ≠ 0 := by
  intro z him hre
  by_cases h1 : 1 ≤ z.re
  ·                                     
    simpa using riemannZeta_ne_zero_of_one_le_re h1
                        
  have hzlt1 : z.re < 1 := lt_of_not_ge h1
                                                 
  have hgt : |z.im| > 2 := by simpa using him
  have hδ := (lem_delta19).1 z hgt
  rcases hδ with ⟨hδ_pos, hδ_lt_19⟩
                                                                  
  have h9δ_lt1 : 9 * deltaz z < 1 := by
    have h := mul_lt_mul_of_pos_left hδ_lt_19 (by norm_num : 0 < (9 : ℝ))
    have h9 : (9 : ℝ) * (1 / 9) = 1 := by norm_num
    simpa [h9] using h
  have hzre_pos : 0 < z.re := by
    have : 0 < 1 - 9 * deltaz z := sub_pos.mpr h9δ_lt1
    exact lt_trans this hre
                                           
  by_contra hzero
  have hzmem : z ∈ zeroZ := by simpa [zeroZ] using hzero
                                                                   
  have hprop := (Classical.choose_spec zerofree).2.2
  have hbound : z.re ≤ 1 - zerofree_constant / Real.log (|z.im| + 2) :=
    hprop z ⟨hzmem, hzre_pos, hzlt1⟩ him
                                           
  set L : ℝ := Real.log (|z.im| + 2) with hLdef
  have hLpos : 0 < L := by
    have hone_lt : (1 : ℝ) < |z.im| + 2 := by
      have : (0 : ℝ) ≤ |z.im| := abs_nonneg _
      linarith
    have := Real.log_pos hone_lt
    simpa [hLdef] using this
                                     
  have hb_le_a' : ((9 : ℝ) / 20) * (zerofree_constant / L) ≤ zerofree_constant / L := by
    have hcoef_le1 : ((9 : ℝ) / 20) ≤ 1 := by norm_num
    have ha_nonneg : 0 ≤ zerofree_constant / L := le_of_lt (div_pos zerofree_constant_pos hLpos)
    have := mul_le_mul_of_nonneg_right hcoef_le1 ha_nonneg
    simpa [one_mul] using this
  have h9d_eq : 9 * deltaz z = ((9 : ℝ) / 20) * (zerofree_constant / L) := by
    simp [deltaz, hLdef, div_eq_mul_inv, mul_left_comm, mul_assoc]
  have hdelta_le : 9 * deltaz z ≤ zerofree_constant / L := by
    simpa [h9d_eq] using hb_le_a'
  have h_le_rhs : 1 - zerofree_constant / L ≤ 1 - 9 * deltaz z := by
    have hneg := neg_le_neg hdelta_le
    simpa [sub_eq_add_neg] using! add_le_add_right hneg 1
                              
  have hle : z.re ≤ 1 - 9 * deltaz z := le_trans hbound h_le_rhs
  have hcontr : z.re < z.re := lt_of_le_of_lt hle hre
  exact (lt_irrefl (z.re)) hcontr

lemma complex_sub_ofReal_I_real_eq_ofReal (z : ℂ) (a t : ℝ) (him : z.im = t) :
  z - ((a : ℂ) + Complex.I * t) = ((z.re - a) : ℂ) := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
  · simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, him]

lemma lem_ZFRinD (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∈ Metric.closedBall c (2/3) := by
  intro c h
  rcases h with ⟨h_low, hrest⟩
  rcases hrest with ⟨h_high, him⟩
  have hsub : z - c = ((z.re - (3/2)) : ℂ) := by
    simpa [c] using! complex_sub_ofReal_I_real_eq_ofReal z (3/2) t him
  have h1 : dist z c = ‖((z.re - (3/2)) : ℂ)‖ := by
    simp [dist_eq_norm, hsub]
  have h2 : ‖((z.re - (3/2)) : ℂ)‖ = ‖z.re - (3/2)‖ := by
    simpa using (Complex.norm_real (z.re - (3/2)))
  have hdist_abs : dist z c = |z.re - (3/2)| := by
    have h4 : dist z c = ‖z.re - (3/2)‖ := h1.trans h2
    simpa [Real.norm_eq_abs] using h4
  have hnonpos : z.re - (3/2) ≤ 0 := sub_nonpos_of_le h_high
  have habs : |z.re - (3/2)| = 3/2 - z.re := by
    have := abs_of_nonpos hnonpos
    simpa [neg_sub] using this
  have hdist_eq : dist z c = 3/2 - z.re := hdist_abs.trans habs
  have h_le : dist z c ≤ 1/2 + deltaz_t t := by
    calc
      dist z c = 3/2 - z.re := hdist_eq
      _ ≤ 3/2 - (1 - deltaz_t t) := by linarith
      _ = 1/2 + deltaz_t t := by ring
  have hδlt : deltaz_t t < 1/9 := (lem_delta19.2 t ht).2
  have h12δ_lt : (1/2 : ℝ) + deltaz_t t < (1/2 : ℝ) + 1/9 := by
    have := add_lt_add_left hδlt (1/2 : ℝ)
    simpa [add_comm, add_left_comm, add_assoc] using this
  have h123_lt : (1/2 : ℝ) + 1/9 < (2/3 : ℝ) := by norm_num
  have h_lt : (1/2 : ℝ) + deltaz_t t < (2/3 : ℝ) := lt_trans h12δ_lt h123_lt
  have hdist_le : dist z c ≤ 2/3 := le_trans h_le (le_of_lt h_lt)
  exact (Metric.mem_closedBall).2 hdist_le

lemma lem_ZFRnotK (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∉ zerosetKfRc (5/6) c riemannZeta := by
  intro c h

  obtain ⟨h_ge, h_le, h_im⟩ := h

  have h_delta_eq : deltaz z = deltaz_t t := by
    rw [deltaz_t, deltaz]
                                              
    congr 1
    congr 1
                                         
    rw [h_im]

    simp only [Complex.mul_I_im, Complex.ofReal_re]

  have h_ge_delta : 1 - deltaz z ≤ Complex.re z := by
    rwa [← h_delta_eq] at h_ge

  have h_im_gt : |z.im| > 2 := by
    rw [h_im]
    exact ht

  have h_delta_pos : 0 < deltaz z := by
    exact (lem_delta19.1 z h_im_gt).1

  have h_delta_lt_9delta : deltaz z < 9 * deltaz z := by
    linarith [h_delta_pos]

  have h_strict : Complex.re z > 1 - 9 * deltaz z := by
    linarith [h_ge_delta, h_delta_lt_9delta]

  have h_zeta_ne_zero : riemannZeta z ≠ 0 :=
    lem_ZFRdelta z h_im_gt h_strict

  intro h_mem
                                                                  
  have h_zero : riemannZeta z = 0 := h_mem.2
                                    
  exact h_zeta_ne_zero h_zero

lemma lem_Zeta_Expansion_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + I * t;
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
        ‖(deriv riemannZeta z / riemannZeta z) -
          (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖
        ≤ C_1 * Real.log |t| := by
  obtain ⟨C, hC_gt_one, hC_expansion⟩ :=
    Zeta1_Zeta_Expansion (2/3) (3/4)
    (by norm_num : (0 : ℝ) < 2/3)
    (by norm_num : (2/3 : ℝ) < 3/4)
    (by norm_num : (3/4 : ℝ) < 5/6)
  let C_1 := C * (1 / ((3/4 : ℝ) - 2/3)^3 + 1)
  have hC_1_gt_1 : C_1 > 1 := by
    have h_coeff : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 + 1 > 1 := by
      have h_pos : ((3/4 : ℝ) - 2/3)^3 > 0 := by norm_num
      have h_div_pos : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 > 0 := div_pos one_pos h_pos
      linarith
    have h_ge_1 : (1 : ℝ) ≤ C := le_of_lt hC_gt_one
    exact one_lt_mul_of_le_of_lt h_ge_1 h_coeff
  refine ⟨C_1, hC_1_gt_1, ?_⟩
  intro t ht c hfin z hz
  have ht2 : |t| > 2 := by linarith
  have hz_in_ball : z ∈ Metric.closedBall c (2/3) := by
    simpa [c] using (lem_ZFRinD t ht2 z hz)
  have hz_not_in_K : z ∉ zerosetKfRc (5/6) c riemannZeta := by
    simpa [c] using (lem_ZFRnotK t ht2 z hz)
  have hz_in_diff : z ∈ Metric.closedBall c (2/3) \ zerosetKfRc (5/6) c riemannZeta :=
    ⟨hz_in_ball, hz_not_in_K⟩
  have h_expansion := hC_expansion t ht hfin z hz_in_diff
  rw [show logDerivZeta z = deriv riemannZeta z / riemannZeta z from rfl] at h_expansion
  exact h_expansion

lemma lem_abszrhoReRe (z ρ : ℂ) : ‖z - ρ‖ ≥ z.re - ρ.re := by
  have h1 : (z - ρ).re ≤ ‖z - ρ‖ := Complex.re_le_norm (z - ρ)
  have h2 : (z - ρ).re = z.re - ρ.re := Complex.sub_re z ρ
  rw [← h2]
  exact h1

lemma lem_Rerhotodeltarho {ρ : ℂ} :
  ∀ t : ℝ, |t| > 3 → ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) (3/2+ t* Complex.I) riemannZeta) → ρ.re ≤ 1 - 9 * deltaz ρ := by
  intro t ht h_mem
                                                   
  have h_zero : riemannZeta ρ = 0 := h_mem.2

  have h_ball : ρ ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6) := h_mem.1

  have h_dist : dist ρ (3/2 + t * Complex.I) ≤ 5/6 := by
    rwa [Metric.mem_closedBall] at h_ball

  have h_im : 2 < |ρ.im| := by
                                                                 
    have h_im_bound : |ρ.im - t| ≤ 5/6 := by
                                         
      have h_le_norm : |ρ.im - t| ≤ ‖ρ - (3/2 + t * Complex.I)‖ := by
        have : |(ρ - (3/2 + t * Complex.I)).im| ≤ ‖ρ - (3/2 + t * Complex.I)‖ :=
          Complex.abs_im_le_norm _
        have h_im_eq : (ρ - (3/2 + t * Complex.I)).im = ρ.im - t := by
          simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im]
        rwa [← h_im_eq]
      rw [← Complex.dist_eq] at h_le_norm
      linarith [h_le_norm, h_dist]

    have triangle := abs_sub_abs_le_abs_sub t ρ.im

    have eq_comm : |t - ρ.im| = |ρ.im - t| := abs_sub_comm t ρ.im
    rw [eq_comm] at triangle

    have h_ge : |ρ.im| ≥ |t| - |ρ.im - t| := by linarith [triangle]

    have : |ρ.im| ≥ |t| - 5/6 := by linarith [h_ge, h_im_bound]
    have : |ρ.im| > 3 - 5/6 := by linarith [ht]
    have h_calc : (3 : ℝ) - 5/6 = 13/6 := by norm_num
    have h_gt2 : (13 : ℝ)/6 > 2 := by norm_num
    rw [h_calc] at *
    linarith [h_gt2]

  have h_not_gt : ¬(ρ.re > 1 - 9 * deltaz ρ) := by
    intro h_gt
    have h_ne_zero := lem_ZFRdelta ρ h_im h_gt
    exact h_ne_zero h_zero

  exact le_of_not_gt h_not_gt

lemma lem_DImt2d :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| ≤ |t| + 5/6 := by
  intro t ht z hz
                                                                  
  rw [Metric.mem_closedBall] at hz
                                    
  have center_im : (3/2 + t * Complex.I).im = t := by simp [Complex.add_im, Complex.mul_im]
                                  
  have diff_im : (z - (3/2 + t * Complex.I)).im = z.im - t := by
    rw [Complex.sub_im, center_im]
                                      
  have h1 : |z.im - t| ≤ ‖z - (3/2 + t * Complex.I)‖ := by
    rw [← diff_im]
    exact Complex.abs_im_le_norm _
                                       
  have h2 : |z.im - t| ≤ 5/6 := le_trans h1 (by simpa only [dist_eq_norm] using! hz)
                                                                                            
  have h3 : |z.im| ≤ |z.im - t| + |t| := by
    conv_lhs => rw [show z.im = (z.im - t) + t by ring]
    exact abs_add_le (z.im - t) t
  linarith

lemma lem_DIMt2 :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| + 2 ≤ (|t| + 2)^3 := by
  intro t ht z hz
                                                
  have h1' := lem_DImt2d t ht z hz
                                     
  have h1a : |z.im| + 2 ≤ |t| + 17/6 := by
    simpa [show |t| + 5/6 + 2 = |t| + 17/6 by ring] using! add_le_add_left h1' 2
                                
  have h17le3 : |t| + 17/6 ≤ |t| + 3 := by
    have : (17 : ℝ) / 6 ≤ 3 := by norm_num
    exact add_le_add_right this _
                                                                    
  have h_nonneg_poly : 0 ≤ |t|^3 + 6 * |t|^2 + 11 * |t| + 5 := by
    have h0 : 0 ≤ |t|^3 := by exact pow_nonneg (abs_nonneg _) 3
    have h1 : 0 ≤ 6 * |t|^2 := by
      have : 0 ≤ (6 : ℝ) := by norm_num
      exact mul_nonneg this (sq_nonneg _)
    have h2 : 0 ≤ 11 * |t| := by
      have : 0 ≤ (11 : ℝ) := by norm_num
      exact mul_nonneg this (abs_nonneg _)
    have h3 : 0 ≤ (5 : ℝ) := by norm_num
    exact add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3
  have h_add : |t| + 3 ≤ (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    simpa using (le_add_of_nonneg_right (a := |t| + 3) h_nonneg_poly)
  have h_expand : (|t| + 2)^3 = (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    ring
  have h3 : |t| + 3 ≤ (|t| + 2)^3 := by
    simpa [h_expand] using h_add
                           
  exact le_trans (le_trans h1a h17le3) h3

lemma lem_DlogImlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    Real.log (|z.im| + 2) ≤ 3 * Real.log (|t| + 2) := by
  intro t ht z hz
                                                                           
  have h1 : |z.im| + 2 ≤ (|t| + 2)^3 := lem_DIMt2 t ht z hz
                                           
  have h2 : 0 < |z.im| + 2 := by
    have : 0 ≤ |z.im| := abs_nonneg _
    linarith
                        
  have hlog := Real.log_le_log h2 h1
                                  
  simpa [Real.log_pow] using hlog

lemma lem_D1logtlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    (1 : ℝ) / Real.log (|t| + 2) ≤ 3 / Real.log (|z.im| + 2) := by
  intro t ht z hz
  have h1 := lem_DlogImlog t ht z hz
                                                     
  have ht_pos : |t| + 2 > 1 := by linarith [abs_nonneg t]
  have hz_pos : |z.im| + 2 > 1 := by linarith [abs_nonneg z.im]
  have log_t_pos : Real.log (|t| + 2) > 0 := Real.log_pos ht_pos
  have log_z_pos : Real.log (|z.im| + 2) > 0 := Real.log_pos hz_pos

  rw [div_le_div_iff₀ log_t_pos log_z_pos]
  simp only [one_mul]
  exact h1

lemma lem_Ddt2dz :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    deltaz_t t ≤ 3 * deltaz z := by
  intro t ht z hz
  have h := lem_D1logtlog t ht z hz
  have hpos : 0 ≤ zerofree_constant / 20 := by
    have ha : 0 < zerofree_constant := zerofree_constant_pos
    have h9 : 0 < (20 : ℝ) := by norm_num
    exact div_nonneg (le_of_lt ha) (le_of_lt h9)
  have h2 := mul_le_mul_of_nonneg_left h hpos
  calc
    deltaz_t t
        = (zerofree_constant / 20) / Real.log (|t| + 2) := by
            simp [deltaz_t, deltaz]
    _ = (zerofree_constant / 20) * (1 / Real.log (|t| + 2)) := by simp [div_eq_mul_inv]
    _ ≤ (zerofree_constant / 20) * (3 / Real.log (|z.im| + 2)) := h2
    _ = 3 * ((zerofree_constant / 20) * (1 / Real.log (|z.im| + 2))) := by
            simp [div_eq_mul_inv, mul_left_comm, mul_assoc]
    _ = 3 * deltaz z := by simp [deltaz, div_eq_mul_inv, mul_left_comm, mul_assoc]

lemma lem_deltarhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → deltaz ρ ≥ (1/3) * deltaz_t t := by
  intro c hρK
  rcases hρK with ⟨hball, _hzero⟩
  have hball' : ρ ∈ Metric.closedBall ((3/2 : ℂ) + t * Complex.I) (5/6) := by
    simpa [c, mul_comm] using! hball
  have hmain : deltaz_t t ≤ 3 * deltaz ρ := lem_Ddt2dz t ht ρ hball'
  have hthird_nonneg : 0 ≤ (1/3 : ℝ) := by norm_num
  have h_mul : (1/3 : ℝ) * deltaz_t t ≤ (1/3 : ℝ) * (3 * deltaz ρ) :=
    mul_le_mul_of_nonneg_left hmain hthird_nonneg
  have h_simplify : (1/3 : ℝ) * (3 * deltaz ρ) = deltaz ρ := by
    ring
  have : (1/3 : ℝ) * deltaz_t t ≤ deltaz ρ := by
    simpa [h_simplify] using h_mul
  simpa [mul_comm] using this

lemma lem_Rerhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → ρ.re ≤ 1 - 3 * deltaz_t t := by
  intros c h_rho_in
                                                          
  have h1 : ρ.re ≤ 1 - 9 * deltaz ρ :=
    lem_Rerhotodeltarho (ρ := ρ) t ht (by simpa [c, mul_comm] using! h_rho_in)
                                                         
  have h2 : deltaz ρ ≥ (1/3) * deltaz_t t := lem_deltarhotodeltat t ht ρ h_rho_in
                                                         
  have h3 : 9 * deltaz ρ ≥ 3 * deltaz_t t := by
    calc
      9 * deltaz ρ
          ≥ 9 * ((1/3) * deltaz_t t) := by
                exact mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 9)
      _ = 9 * (1/3) * deltaz_t t := by ring
      _ = 3 * deltaz_t t := by norm_num
                                         
  have h4 : 1 - 9 * deltaz ρ ≤ 1 - 3 * deltaz_t t := by
    linarith [h3]
                                                        
  exact le_trans h1 h4

lemma lem_RezRerho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    z.re - ρ.re ≥ 2 * deltaz_t t := by
  intro c h_rho_mem h_z
                                                     
  have h_rho_bound := lem_Rerhotodeltat t ht ρ h_rho_mem
                                                
  have h_z_lower := h_z.1
                                                                                      
  linarith [h_z_lower, h_rho_bound]

lemma lem_abszrhodelta (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖z - ρ‖ ≥ 2 * deltaz_t t := by
  intro c h_rho_in_K h_z_conditions
                                                         
  have h1 : z.re - ρ.re ≥ 2 * deltaz_t t := (lem_RezRerho t ht z ρ) h_rho_in_K h_z_conditions
                                                     
  have h2 : ‖z - ρ‖ ≥ z.re - ρ.re := lem_abszrhoReRe z ρ
                                                                    
  exact le_trans h1 h2

lemma lem_1abszrho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) := by
  intro c hρ hz
                                                              
  apply one_div_le_one_div_of_le
                                           
  · have h_delta_pos : 0 < deltaz_t t := by
      have h_delta19 := lem_delta19
      exact (h_delta19.2 t (by linarith [ht] : |t| > 2)).1
    linarith [h_delta_pos]
                                                  
  · exact lem_abszrhodelta t ht z ρ hρ hz

lemma lem_finiteKzeta (t : ℝ) (_ht : |t| > 3) :
    let c := (3/2 : ℂ) + I * t
    (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite := by
  intro c
  have hK : IsCompact (Metric.closedBall c (5 / (6 : ℝ))) :=
    closedBall_compact_complex c (5 / (6 : ℝ))
  simpa [zerosetKfRc] using
    (riemannZeta_zeros_finite_of_compact (Metric.closedBall c (5 / (6 : ℝ))) hK)

lemma lem_triangle_ZFR (t : ℝ) (_ht : |t| > 3) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ ≤
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) := by
                                                                                                  
  intros c hfin hz_cond

  apply le_trans (norm_sum_le _ _)

  apply Finset.sum_le_sum
  intro ρ hρ

  rw [norm_div]

  rw [Complex.norm_natCast]

lemma lem_Zeta_Triangle_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + I * t
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
        ‖deriv riemannZeta z / riemannZeta z‖ ≤
        ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ +
        C_1 * Real.log |t| := by
  obtain ⟨C1, hC1, hbound⟩ := lem_Zeta_Expansion_ZFR
  refine ⟨C1, hC1, ?_⟩
  intro t ht c hfin z hz
                                           
  let S := (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))
  have hbound1 := hbound t ht hfin z hz
  have htri : ‖deriv riemannZeta z / riemannZeta z‖ ≤ ‖(deriv riemannZeta z / riemannZeta z) - S‖ + ‖S‖ := by
    have hn := norm_add_le ((deriv riemannZeta z / riemannZeta z) - S) S
    have hrewrite : (deriv riemannZeta z / riemannZeta z) - S + S = (deriv riemannZeta z / riemannZeta z) := by
      simp [sub_eq_add_neg]
    simpa [S, hrewrite] using hn
  have hsum := add_le_add_left hbound1 ‖S‖
  have : ‖deriv riemannZeta z / riemannZeta z‖ ≤ C1 * Real.log |t| + ‖S‖ := le_trans htri hsum
  simpa [S, add_comm] using this

lemma lem_sumK1abs (t : ℝ) (ht : |t| > 3) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
    (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) := by
  intro c hfin hzcond
                                       
  have hptwise : ∀ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖ ≤
      (1 / (2 * deltaz_t t)) * ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
    intro ρ hρmem
    have hρ_in : ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρmem
    have hbase : 1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) :=
      lem_1abszrho t ht z ρ hρ_in hzcond
    have hnonneg : 0 ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
      exact_mod_cast (Nat.zero_le ((analyticOrderAt riemannZeta ρ).toNat))
    have := mul_le_mul_of_nonneg_left hbase hnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hsum := Finset.sum_le_sum hptwise
                                                                
  have hrw :=
    (Finset.mul_sum (s := hfin.toFinset)
      (f := fun ρ => ((analyticOrderAt riemannZeta ρ).toNat : ℝ))
      (a := (1 / (2 * deltaz_t t))))
  have hsum2 := hsum
                                                        
  rw [← hrw] at hsum2
           
  simpa [div_eq_mul_inv] using hsum2

lemma helper_analyticOnNhd_shift_div (f : ℂ → ℂ) (c : ℂ)
    (h : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z)
    (_hc : f c ≠ 0) :
    AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (Metric.closedBall (0 : ℂ) 1) := by
                                                                                     
  intro z hz
                                                 
  have hz_norm : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
                                                                   
  have hz_addc_mem : z + c ∈ Metric.closedBall c 1 := by
                                           
    have : dist (z + c) c ≤ 1 := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz_norm
    simpa [Metric.mem_closedBall] using this
                                               
  have h_f_at : AnalyticAt ℂ f (z + c) := h (z + c) hz_addc_mem
                                               
  have h_addc : AnalyticAt ℂ (fun w => w + c) z := by
    simpa using! (analyticAt_id.add analyticAt_const)
                                                              
  have h_comp : AnalyticAt ℂ (fun w => f (w + c)) z :=
    (AnalyticAt.fun_comp h_f_at h_addc)
                                                                                            
  have h_mul_const : AnalyticAt ℂ (fun w => (1 / f c) * f (w + c)) z :=
    (analyticAt_const.mul h_comp)
                                
  simpa [div_eq_mul_inv, mul_comm] using h_mul_const

lemma helper_bound_shifted (B R : ℝ) (_hB : 1 < B) (_hRpos : 0 < R) (_hRlt1 : R < 1)
    (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
    (h_bound : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ :=
by
  intro z hz
                                            
  have hz_norm : ‖z‖ ≤ R := by
    have hz' : dist z (0 : ℂ) ≤ R := by simpa [Metric.mem_closedBall] using hz
    simpa [Complex.dist_eq] using hz'
                                 
  have hz_ballc : z + c ∈ Metric.closedBall c R := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel] using hz_norm
                                                  
  have hfb : ‖f (z + c)‖ ≤ B := h_bound (z + c) hz_ballc
                                        
  have hpos : 0 < ‖f c‖ := (norm_pos_iff).2 hc
                                   
  have hdiv : ‖f (z + c)‖ / ‖f c‖ ≤ B / ‖f c‖ := (div_le_div_iff_of_pos_right hpos).2 hfb
                                              
  have hnorm_eq : ‖(fun w => f (w + c) / f c) z‖ = ‖f (z + c)‖ / ‖f c‖ := by
    change ‖f (z + c) / f c‖ = ‖f (z + c)‖ / ‖f c‖
    simp
  simpa [hnorm_eq] using hdiv

lemma helper_g_zero_eq_one (f : ℂ → ℂ) (c : ℂ) (hc : f c ≠ 0) :
  (fun z => f (z + c) / f c) 0 = 1 := by
  simp [hc]

lemma helper_zerosetKfR_eq_center0 (r : ℝ) (hr : r > 0) (f : ℂ → ℂ) :
  zerosetKfR r hr f = zerosetKfRc r (0 : ℂ) f := by
  ext ρ; simp [zerosetKfR, zerosetKfRc]

lemma helper_apply_jensen_to_g
  (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_ne : g 0 ≠ 0)
  (hg0_one : g 0 = 1)
  (hfin_g : (zerosetKfR R1 (by linarith) g).Finite)
  (hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B) :
  (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) ≤ Real.log B / Real.log (R / R1) := by
  classical
                                                     
  have h_exists : ∀ σ ∈ zerosetKfR R1 (by linarith) g,
      ∃ hσ : ℂ → ℂ, AnalyticAt ℂ hσ σ ∧ hσ σ ≠ 0 ∧
        ∀ᶠ z in nhds σ, g z = (z - σ) ^ (analyticOrderAt g σ).toNat * hσ z := by
    intro σ hσ
    exact lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR_lt_1 g h_g_analytic hg0_ne σ hσ
                                            
  let h_σ : ℂ → (ℂ → ℂ) :=
    fun σ => dite (σ ∈ zerosetKfR R1 (by linarith) g)
      (fun h => Classical.choose (h_exists σ h))
      (fun _ => fun _ => (1 : ℂ))
                                             
  have h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) g,
      AnalyticAt ℂ (h_σ σ) σ ∧ (h_σ σ) σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, g z = (z - σ) ^ (analyticOrderAt g σ).toNat * (h_σ σ) z := by
    intro σ hσin
    have hx := h_exists σ hσin
    dsimp [h_σ]
                                  
    simpa [hσin] using (Classical.choose_spec hx)
                                      
  have hbound :=
    lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1
      g h_g_analytic hg0_ne hg0_one hfin_g (h_σ := h_σ) hg_le_B h_σ_spec
                                         
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbound

lemma helper_sum_f_equals_sum_g
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
  (hfin : (zerosetKfRc r c f).Finite) :
  (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
  =
  (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
      ((analyticOrderAt (fun z => f (z + c) / f c) ρ').toNat : ℝ)) :=
by
  classical
             
  let S : Finset ℂ := hfin.toFinset
  let φ : ℂ → ℂ := fun ρ => ρ - c
  let g' : ℂ → ℂ := fun z => f (z + c) / f c

  have himg : (φ '' zerosetKfRc r c f).Finite := hfin.image φ
  have h_img_toFinset : ((hfin.image φ).toFinset) = S.image φ := by
    simpa [S] using (Set.Finite.toFinset_image (s := (zerosetKfRc r c f)) (f := φ)
      (hs := hfin) (h := himg))

  have h_orders_match :
      (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ)) =
      (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρS
                                                                          
    have hρ_mem : ρ ∈ zerosetKfRc r c f :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρS
    have hρ_ball : ρ ∈ Metric.closedBall c r := hρ_mem.1
    have hρ_fzero : f ρ = 0 := hρ_mem.2
                                                                   
    have hρ'_ball : (φ ρ) ∈ Metric.closedBall (0 : ℂ) r := by
                     
      have hdist_le : dist ρ c ≤ r := by
        simpa [Metric.mem_closedBall] using hρ_ball
                                               
      have : dist (φ ρ) 0 ≤ r := by
        simpa [φ, dist_eq_norm] using (by simpa [dist_eq_norm] using hdist_le)
      simpa [Metric.mem_closedBall] using this
    have hρ'_gzero : g' (φ ρ) = 0 := by
      simp [g', φ, hρ_fzero, sub_eq_add_neg, add_comm]
    have hρ'_mem : (φ ρ) ∈ zerosetKfRc r (0 : ℂ) g' := ⟨hρ'_ball, hρ'_gzero⟩
                                                
    have h_m_eq := fc_m_order r hr c f hc h_analytic (ρ' := φ ρ) hρ'_mem
                    
    have h_m_eq' : analyticOrderAt g' (φ ρ) = analyticOrderAt f ρ := by
      simpa [g', φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_m_eq
                                  
    have h_toNat : (analyticOrderAt g' (φ ρ)).toNat = (analyticOrderAt f ρ).toNat := by
      simpa using congrArg ENat.toNat h_m_eq'
    simp [h_toNat]

  have h_inj : Function.Injective φ := by
    intro x y hxy
                                                    
    have := congrArg (fun z => z + c) hxy
    simpa [φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

  have h_sum_image :
      (∑ ρ' ∈ S.image φ, ((analyticOrderAt g' ρ').toNat : ℝ)) =
      (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := by
    refine Finset.sum_image ?h
    intro x hx y hy hxy
                                
    exact h_inj hxy

  calc
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
        = (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ)) := by rfl
    _ = (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := h_orders_match
    _ = (∑ ρ' ∈ S.image φ, ((analyticOrderAt g' ρ').toNat : ℝ)) := h_sum_image.symm
    _ = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderAt (fun z => f (z + c) / f c) ρ').toNat : ℝ)) := by
                                                     
          simp [S, φ, g', h_img_toFinset]

lemma helper_zero_set_shift_eq
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1)) :
  zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
  = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  simpa using fc_zeros r hr c f hc h_analytic

lemma helper_fin_zero_g_is_image
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
  (hfin : (zerosetKfRc r c f).Finite) :
  (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)).Finite :=
by
  classical
  have hset : zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
      = (fun ρ => ρ - c) '' (zerosetKfRc r c f) :=
    by simpa using fc_zeros r hr c f hc h_analytic
  have hfin_img : ((fun ρ => ρ - c) '' (zerosetKfRc r c f)).Finite := hfin.image _
  simpa [hset] using hfin_img

lemma helper_AnalyticOnNhd_to_pointwise {S : Set ℂ} {f : ℂ → ℂ}
  (h : AnalyticOnNhd ℂ f S) : ∀ z ∈ S, AnalyticAt ℂ f z := by
  intro z hz
  exact h z hz

lemma jensen_sum_bound_strict
  (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_ne : g 0 ≠ 0)
  (hg0_one : g 0 = 1)
  (hfin_g : (zerosetKfR R1 (by linarith) g).Finite)
  (hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B) :
  (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) ≤
    Real.log B / Real.log (R / R1) := by
  exact helper_apply_jensen_to_g B R R1 hB hR1_pos hR1_lt_R hR_lt_1 g
    h_g_analytic hg0_ne hg0_one hfin_g hg_le_B

lemma no_zero_of_bound_one_and_center_one
  (R : ℝ) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_one : g 0 = 1)
  (hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1) :
  ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 := by
  intro z hz
  by_cases hRpos : 0 < R
  ·
                                             
    have hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) := by
      intro x hx
      have hxlt : ‖x‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans (le_of_lt hxlt) (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact ((h_g_analytic x hx_in1).differentiableAt).differentiableWithinAt
                                                
    have hcont : ContinuousOn g (Metric.closedBall (0 : ℂ) R) := by
      intro x hx
      have hxleR : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans hxleR (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact (h_g_analytic x hx_in1).continuousAt.continuousWithinAt
    have hdcc : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) :=
      DiffContOnCl.mk_ball hdiff hcont
                                                               
    have hIsMax : IsMaxOn (fun z => ‖g z‖) (Metric.ball (0 : ℂ) R) 0 := by
      intro y hy
      have hynormlt : ‖y‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hy
      have hyle : ‖y‖ ≤ R := le_of_lt hynormlt
      have hgy : ‖g y‖ ≤ 1 := hg_le_one y hyle
      simpa [hg0_one] using hgy
                                                         
    have hEqOn :=
      Complex.eqOn_closedBall_of_isMaxOn_norm (z := (0 : ℂ)) (r := R) hdcc hIsMax
    have hz_eq : g z = (fun _ => g 0) z := hEqOn hz
    have hz_eq1 : g z = g 0 := by simpa using hz_eq
    have gz_one : g z = 1 := by simpa [hg0_one] using hz_eq1
    simp [gz_one]
  ·
                                                                           
    have hRle : R ≤ 0 := le_of_not_gt hRpos
    have hz_le : ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
    have hz_norm_eq : ‖z‖ = 0 :=
      le_antisymm (le_trans hz_le hRle) (norm_nonneg z)
    have hz_zero : z = 0 := by
      simpa [norm_eq_zero] using hz_norm_eq
    simp [hz_zero, hg0_one]

lemma helper_sum_over_equal_finite_sets_orders
  {S T : Set ℂ} (g : ℂ → ℂ)
  (hS : S.Finite) (hT : T.Finite) (hST : S = T) :
  (∑ x ∈ hS.toFinset, ((analyticOrderAt g x).toNat : ℝ))
  = (∑ x ∈ hT.toFinset, ((analyticOrderAt g x).toNat : ℝ)) := by
  classical
  have hF : hS.toFinset = hT.toFinset := by
    ext x
    simp [Set.Finite.mem_toFinset, hST]
  simp [hF]

lemma helper_bound_on_ball_to_norm_imp
  {R : ℝ} {g : ℂ → ℂ} {M : ℝ}
  (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ M) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ M := by
  intro z hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R := by
    have : dist z (0 : ℂ) ≤ R := by
      simpa [dist_eq_norm] using hz
    simpa [Metric.mem_closedBall] using this
  exact hg z hz'

lemma helper_pointwise_to_AnalyticOnNhd {S : Set ℂ} {f : ℂ → ℂ}
  (h : ∀ z ∈ S, AnalyticAt ℂ f z) : AnalyticOnNhd ℂ f S := by
  simpa using! h

lemma lem_sum_m_rho_bound_c (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1)
  (hR1_lt_R : R1 < R)
  (hR_lt_1 : R < 1)
  (f : ℂ → ℂ)
  (c : ℂ)
  (h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z)
  (h_f_nonzero_at_zero : f c ≠ 0)
  (hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B)
  (hfin : (zerosetKfRc R1 c f).Finite) :
      ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
  classical
                                                   
  let g : ℂ → ℂ := fun z => f (z + c) / f c

  have h_g_analyticOn : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
    helper_analyticOnNhd_shift_div f c h_f_analytic h_f_nonzero_at_zero
  have h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z :=
    helper_AnalyticOnNhd_to_pointwise h_g_analyticOn

  have hg0_one : g 0 = 1 := helper_g_zero_eq_one f c h_f_nonzero_at_zero
  have hg0_ne : g 0 ≠ 0 := by simp [hg0_one]

  have hAnal_f : AnalyticOnNhd ℂ f (Metric.closedBall c 1) :=
    helper_pointwise_to_AnalyticOnNhd h_f_analytic
  have hfin_g0 : (zerosetKfRc R1 (0 : ℂ) g).Finite :=
    helper_fin_zero_g_is_image R1 hR1_pos c f h_f_nonzero_at_zero hAnal_f hfin
  have hZR_eq : zerosetKfR R1 hR1_pos g = zerosetKfRc R1 (0 : ℂ) g :=
    helper_zerosetKfR_eq_center0 R1 hR1_pos g
  have hfin_g : (zerosetKfR R1 (by exact hR1_pos) g).Finite := by
    simpa [hZR_eq] using hfin_g0

  have h_bound_shift : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_shifted B R hB (by exact lt_trans hR1_pos hR1_lt_R) hR_lt_1 c f
      h_f_nonzero_at_zero (fun z hz => hf_le_B z <| by simpa using hz)
  have hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_on_ball_to_norm_imp (R := R) (g := g) (M := B / ‖f c‖) h_bound_shift

  have hfc_le : ‖f c‖ ≤ B := by
    have : c ∈ Metric.closedBall c R := by
      have hRpos' : 0 ≤ R := le_of_lt (lt_trans hR1_pos hR1_lt_R)
      have : dist c c ≤ R := by simpa [dist_self] using hRpos'
      simpa [Metric.mem_closedBall] using this
    exact hf_le_B c this
  have hfc_pos : 0 < ‖f c‖ := (norm_pos_iff).2 h_f_nonzero_at_zero
  have hBdiv_ge_one : 1 ≤ B / ‖f c‖ := by
    have hdiv := (div_le_div_iff_of_pos_right hfc_pos).mpr hfc_le
    simpa [div_self (ne_of_gt hfc_pos)] using hdiv

  have hsum_fg_eq :
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
        = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderAt g ρ').toNat : ℝ)) :=
    helper_sum_f_equals_sum_g (r := R1) (hr := hR1_pos) (c := c)
      (f := f) (hc := h_f_nonzero_at_zero) (h_analytic := hAnal_f) (hfin := hfin)

  have hST_g_img : zerosetKfR R1 hR1_pos g
      = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) := by
    have h1 : zerosetKfR R1 hR1_pos g = zerosetKfRc R1 (0 : ℂ) g :=
      helper_zerosetKfR_eq_center0 R1 hR1_pos g
    have h2 : zerosetKfRc R1 (0 : ℂ) g
        = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) :=
      helper_zero_set_shift_eq R1 hR1_pos c f h_f_nonzero_at_zero hAnal_f
    simpa [h1] using h2

  rcases lt_or_eq_of_le hBdiv_ge_one with hBdiv_gt_one | hBdiv_eq_one
  ·                                                            
    have hsum_g_bound :=
      jensen_sum_bound_strict (B := B / ‖f c‖) (R := R) (R1 := R1)
        (hB := hBdiv_gt_one)
        (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
        (g := g) (h_g_analytic := h_g_analytic) (hg0_ne := hg0_ne)
        (hg0_one := hg0_one) (hfin_g := hfin_g) (hg_le_B := hg_le_B)
                                                                           
    have hsum_g_reindex :
        (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          = (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 hR1_pos g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
                                                                     
    have :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simpa [hsum_g_reindex] using hsum_g_bound
                                              
    simpa [hsum_fg_eq] using this
  ·                                                                                    
    have hBdiv_eq_one' : B / ‖f c‖ = 1 := by
      simpa [eq_comm] using hBdiv_eq_one
    have hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1 := by
      intro z hz
      have := hg_le_B z hz
      simpa [hBdiv_eq_one'] using this
    have g_nonzero_on_ball : ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 :=
      no_zero_of_bound_one_and_center_one R hR_lt_1 g h_g_analytic hg0_one hg_le_one
                                                                      
    have hS_empty : zerosetKfR R1 hR1_pos g = (∅ : Set ℂ) := by
      ext z; constructor
      · intro hz
        rcases hz with ⟨hzball, hzzero⟩
        have hzR1 : ‖z‖ ≤ R1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
        have hzR : ‖z‖ ≤ R := le_trans hzR1 (le_of_lt hR1_lt_R)
        have hzR' : z ∈ Metric.closedBall (0 : ℂ) R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
        exact (g_nonzero_on_ball z hzR') hzzero
      · intro hzfalse
        cases hzfalse
    have hsum_g_zero :
        (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) = 0 := by
      have h :=
        helper_sum_over_equal_finite_sets_orders (g := g)
          (S := zerosetKfR R1 hR1_pos g) (T := (∅ : Set ℂ))
          (hS := hfin_g) (hT := Set.finite_empty) (hST := hS_empty)
      simpa using h
                                                                                         
    have hsum_reindex :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 hR1_pos g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
    have hsum_img_eq :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          = (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) := by
      simpa using hsum_reindex.symm
    have hsum_img_zero :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) = 0 := by
      simp [hsum_img_eq, hsum_g_zero]
                                                  
    have hsum_f_zero :
        (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) = 0 := by
      simpa [hsum_img_zero] using hsum_fg_eq
                                                   
    have hRHS_zero : Real.log (B / ‖f c‖) / Real.log (R / R1) = 0 := by
      simp [hBdiv_eq_one']
                                      
    have :
        (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simp [hsum_f_zero, hRHS_zero]
    exact this

lemma lem_sum_m_rho_zeta :
    ∃ C_2 > 1, ∀ (t : ℝ) (_ht : |t| > 3),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ C_2 * Real.log |t| := by
  classical
                                    
  obtain ⟨b, hb_gt1, hb_bound⟩ := zeta32upper
  obtain ⟨a, ha_pos, ha_bound⟩ := zeta_low_332
          
  let R1 : ℝ := 5 / 6
  let R : ℝ := 8 / 9
  let logRatio : ℝ := Real.log (R / R1)
                                 
  let u : ℝ := Real.log (b / a)
  let C2 : ℝ := max 2 ((1 + |u|) / logRatio)
  have hC2_gt_one : 1 < C2 := by
    have htwo_lt : (1 : ℝ) < 2 := by norm_num
    have hle : (2 : ℝ) ≤ C2 := by
      have := le_max_left (2 : ℝ) ((1 + |u|) / logRatio)
      simp [C2]
    exact lt_of_lt_of_le htwo_lt hle
  refine ⟨C2, hC2_gt_one, ?_⟩
  intro t ht c hfin
                              
  have hR1_pos : 0 < R1 := by dsimp [R1] <;> norm_num
  have hR1_lt_R : R1 < R := by dsimp [R1, R] <;> norm_num
  have hR_lt_1 : R < 1 := by dsimp [R] <;> norm_num
  have hR_le_one : R ≤ (1 : ℝ) := by dsimp [R] <;> norm_num
                                                                                          
  have ht1 : |t| > 1 := lt_trans (by norm_num) ht
  have h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ riemannZeta z := by
    intro z hz
    have hz_ne_one : z ≠ (1 : ℂ) := (D1cinTt_pre t ht1) z (by simpa [c] using hz)
    exact zetaanalOnnot1 z hz_ne_one
                      
  have h_nonzero : riemannZeta c ≠ 0 := by simpa [c] using zetacnot0 t
                                                          
  have ht2 : |t| > 2 := by linarith
  have h_upper_on_ball1 : ∀ z ∈ Metric.closedBall c 1, ‖riemannZeta z‖ < b * |t| := by
    have h := hb_bound t ht2
    intro z hz; simpa [c] using h z (by simpa [c] using hz)
  have hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖riemannZeta z‖ ≤ b * |t| := by
    intro z hz
    have hz1 : z ∈ Metric.closedBall c 1 :=
      (Metric.closedBall_subset_closedBall hR_le_one) hz
    exact le_of_lt (h_upper_on_ball1 z hz1)
                         
  have hb_pos : 0 < b := lt_trans (by norm_num) hb_gt1
  have htabove1 : (1 : ℝ) ≤ |t| := le_of_lt ht1
  have hb_le_B : b ≤ b * |t| := by
    have := mul_le_mul_of_nonneg_left htabove1 (le_of_lt hb_pos)
    simpa [one_mul] using this
  have hBpos : 1 < b * |t| := lt_of_lt_of_le hb_gt1 hb_le_B
                                                                  
  have h_sum_bound :=
    lem_sum_m_rho_bound_c (B := b * |t|) (R := R) (R1 := R1)
      (hB := hBpos)
      (hR1_pos := hR1_pos)
      (hR1_lt_R := hR1_lt_R)
      (hR_lt_1 := hR_lt_1)
      (f := riemannZeta) (c := c)
      (h_f_analytic := h_f_analytic)
      (h_f_nonzero_at_zero := h_nonzero)
      (hf_le_B := hf_le_B)
      (hfin := hfin)
                           
  have hlogRatio_pos : 0 < logRatio := by
    have : 1 < R / R1 := by dsimp [R, R1] <;> norm_num
    exact Real.log_pos this
                          
  have h_zeta_ge_a : a ≤ ‖riemannZeta c‖ := by
    simpa [c, mul_comm] using! ha_bound t

  have ht_abs_pos : 0 < |t| := lt_trans (by norm_num) ht
  have hζ_norm_pos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr h_nonzero
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have ht_abs_ne : (|t| : ℝ) ≠ 0 := ne_of_gt ht_abs_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hlog_split1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        = (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖ := by
    have : Real.log (b * |t|) = Real.log b + Real.log |t| :=
      Real.log_mul hb_ne ht_abs_ne
    have :
        Real.log ((b * |t|) / ‖riemannZeta c‖)
          = Real.log (b * |t|) - Real.log ‖riemannZeta c‖ :=
      Real.log_div (by exact mul_ne_zero hb_ne ht_abs_ne) (ne_of_gt hζ_norm_pos)
    simp [this, Real.log_mul hb_ne ht_abs_ne]
  have hlog_div_eq : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div hb_ne ha_ne
  have hlog_a_le : Real.log a ≤ Real.log ‖riemannZeta c‖ :=
    Real.log_le_log (by exact ha_pos) (by exact h_zeta_ge_a)
  have hneg : -(Real.log ‖riemannZeta c‖) ≤ -Real.log a := by
    simpa using (neg_le_neg hlog_a_le)
  have hRHS_le_const :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        ≤ Real.log |t| + Real.log (b / a) := by
                                       
    have :
        (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖
          ≤ (Real.log b + Real.log |t|) - Real.log a := by
      simpa [sub_eq_add_neg] using! add_le_add_right hneg (Real.log b + Real.log |t|)
    simpa [hlog_split1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hlog_div_eq]
      using this
                                
  have hRHS1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖) / logRatio
        ≤ (Real.log |t| + Real.log (b / a)) / logRatio := by
    exact div_le_div_of_nonneg_right hRHS_le_const (le_of_lt hlogRatio_pos)
                                   
  have hlogt_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                          
    have h3le : (3 : ℝ) ≤ |t| := le_of_lt ht
    have hlog3_le : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) h3le
    have h_exp_le : Real.exp (1 : ℝ) ≤ 3 := le_of_lt lem_three_gt_e
    have hlog3_ge_one : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : 0 < (3 : ℝ))).mpr h_exp_le
    exact le_trans hlog3_ge_one hlog3_le
  have hadd_le : Real.log |t| + Real.log (b / a) ≤ (1 + |u|) * Real.log |t| := by
    have haux1 : Real.log (b / a) ≤ |u| := by simpa [u] using le_abs_self (Real.log (b / a))
    have haux2 : |u| ≤ |u| * Real.log |t| := by
      have hnonneg : 0 ≤ |u| := abs_nonneg _
      have h1le : (1 : ℝ) ≤ Real.log |t| := hlogt_ge_one
      simpa [one_mul] using (mul_le_mul_of_nonneg_left h1le hnonneg)
    calc
      Real.log |t| + Real.log (b / a)
          ≤ Real.log |t| + |u| := by exact add_le_add_right haux1 _
      _ ≤ Real.log |t| + (|u| * Real.log |t|) := by exact add_le_add_right haux2 _
      _ = (1 + |u|) * Real.log |t| := by ring
  have hRHS2 :
      (Real.log |t| + Real.log (b / a)) / logRatio
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := div_le_div_of_nonneg_right hadd_le (le_of_lt hlogRatio_pos)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hfinal :
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ))
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := le_trans h_sum_bound hRHS1
    exact le_trans this hRHS2
                              
  have hC2_ge : ((1 + |u|) / logRatio) ≤ C2 := by
    have := le_max_right (2 : ℝ) ((1 + |u|) / logRatio)
    simp [C2]
  have hlogt_nonneg : 0 ≤ Real.log |t| := le_trans (by norm_num) hlogt_ge_one
  have hscale := mul_le_mul_of_nonneg_right hC2_ge hlogt_nonneg
  exact le_trans hfinal hscale

lemma lem_sumKdeltatlogt :
  ∃ C_3 > 1, ∀ (t : ℝ) (_ht : |t| > 3),
  let c := (3/2 : ℂ) + I * t;
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
      (C_3 / (deltaz_t t)) * Real.log |t| := by
                                        
  obtain ⟨C_2, hC_2_pos, hC_2_bound⟩ := lem_sum_m_rho_zeta

  use C_2

  constructor
  ·                                             
    exact hC_2_pos

  ·              
    intro t ht c hfin z hz

    have h1 := lem_sumK1abs t ht z hfin hz

    have h2 := hC_2_bound t ht hfin

    have ht2 : |t| > 2 := by linarith [ht]
    have h_delta_pos : 0 < deltaz_t t := (lem_delta19.2 t ht2).1

    have h_t_ge_one : (1 : ℝ) ≤ |t| := by linarith [ht]

    calc
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖)
        ≤ (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) := h1
      _ ≤ (1 / (2 * deltaz_t t)) * (C_2 * Real.log |t|) := by
          apply mul_le_mul_of_nonneg_left h2
          apply div_nonneg (by norm_num)
          apply mul_nonneg (by norm_num) (le_of_lt h_delta_pos)
      _ = (C_2 / (2 * deltaz_t t)) * Real.log |t| := by ring
      _ ≤ (C_2 / deltaz_t t) * Real.log |t| := by
          apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg h_t_ge_one)
                                                           
          apply div_le_div_of_nonneg_left (le_of_lt (lt_trans zero_lt_one hC_2_pos))
          · exact h_delta_pos
          ·                                    
            calc deltaz_t t
              = 1 * deltaz_t t := by rw [one_mul]
            _ ≤ 2 * deltaz_t t := by
              apply mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt h_delta_pos)

lemma lem_sumKlogt2 :
  ∃ C_4 > 1, ∀ (t : ℝ) (_ht : |t| > 3),
  let c := (3/2 : ℂ) + I * t
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
      C_4 * Real.log |t|^2 := by
                                        
  obtain ⟨C_3, hC_3_gt, hC_3⟩ := lem_sumKdeltatlogt

  use max (100 * C_3 / zerofree_constant) 2

  constructor
  · exact lt_max_of_lt_right (by norm_num : (2 : ℝ) > 1)

  · intro t ht c hfin z hz
                                              
    have h_bound := hC_3 t ht hfin z hz

    have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
    have h_log_t_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
    have hC_3_pos : 0 < C_3 := lt_trans zero_lt_one hC_3_gt
    have h_zerofree_pos : 0 < zerofree_constant := zerofree_constant_pos

    have h_log_bound : Real.log (|t| + 2) ≤ 2 * Real.log |t| := by
      have h_ineq : |t| + 2 ≤ 2 * |t| := by linarith [ht]
      have h_log_ineq := Real.log_le_log (by linarith [abs_nonneg t] : 0 < |t| + 2) h_ineq
      rw [Real.log_mul (by norm_num) (ne_of_gt h_t_pos)] at h_log_ineq
      have h_log2_bound : Real.log 2 ≤ Real.log |t| :=
        Real.log_le_log (by norm_num) (by linarith [ht] : (2 : ℝ) ≤ |t|)
      linarith [h_log_ineq]

    have h_deltaz_eq : deltaz_t t = (zerofree_constant / 20) / Real.log (|t| + 2) := by
      simp [deltaz_t, deltaz]

    have h_main_bound : C_3 / deltaz_t t * Real.log |t| ≤
                        40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by
                                       
      rw [h_deltaz_eq]

      have h_div_rewrite : C_3 / ((zerofree_constant / 20) / Real.log (|t| + 2)) =
                          C_3 * Real.log (|t| + 2) * 20 / zerofree_constant := by
        field_simp [ne_of_gt h_zerofree_pos, ne_of_gt (Real.log_pos (by linarith [abs_nonneg t] : (1 : ℝ) < |t| + 2))]

      rw [h_div_rewrite]
                                                 
      have h_pos_factor : 0 ≤ C_3 * 20 / zerofree_constant :=
        div_nonneg (mul_nonneg (le_of_lt hC_3_pos) (by norm_num)) (le_of_lt h_zerofree_pos)

      calc C_3 * Real.log (|t| + 2) * 20 / zerofree_constant * Real.log |t|
          = C_3 * 20 / zerofree_constant * Real.log (|t| + 2) * Real.log |t| := by ring
      _ ≤ C_3 * 20 / zerofree_constant * (2 * Real.log |t|) * Real.log |t| := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_log_bound h_pos_factor)
                (le_of_lt h_log_t_pos)
      _ = 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by simp [pow_two]; ring

    calc (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖)
        ≤ C_3 / deltaz_t t * Real.log |t| := h_bound
    _ ≤ 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := h_main_bound
    _ ≤ max (100 * C_3 / zerofree_constant) 2 * (Real.log |t|)^2 := by
        have h_factor_bound : 40 * C_3 / zerofree_constant ≤ max (100 * C_3 / zerofree_constant) 2 := by
          have h_coeff_ineq : 40 * C_3 ≤ 100 * C_3 := by
                                                                                     
            have h_coeff : (40 : ℝ) ≤ 100 := by norm_num
            exact mul_le_mul_of_nonneg_right h_coeff (le_of_lt hC_3_pos)
          have h_div_ineq : 40 * C_3 / zerofree_constant ≤ 100 * C_3 / zerofree_constant := by
                                          
            exact div_le_div_of_nonneg_right h_coeff_ineq (le_of_lt h_zerofree_pos)
          exact le_trans h_div_ineq (le_max_left _ _)
        exact mul_le_mul_of_nonneg_right h_factor_bound (sq_nonneg _)

lemma lem_logDerivZetalogt0 :
  ∃ C > 1,
  ∀ (t : ℝ) (_ht : |t| > 3),
    ∀ s : ℂ, (1 - deltaz_t t) ≤ s.re ∧ s.re ≤ 3/2 ∧ s.im = t →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log |t|^2 := by
                                                              
  obtain ⟨C_1, hC_1_gt, hC_1⟩ := lem_Zeta_Triangle_ZFR
  obtain ⟨C_4, hC_4_gt, hC_4⟩ := lem_sumKlogt2

  use C_1 + C_4

  constructor
  ·               
    linarith [hC_1_gt, hC_4_gt]

  ·              
    intro t ht s hs

    let c := (3/2 : ℂ) + I * t
    have hfin := lem_finiteKzeta t ht

    have h_triangle := hC_1 t ht hfin s hs

    have h_triangle_ineq := lem_triangle_ZFR t ht s hfin hs

    have h_sum_bound := hC_4 t ht hfin s hs

    have h_log_sq_ge : Real.log |t| ≤ Real.log |t|^2 := by
      have h_log_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                                                         
        have h_t_gt_e : Real.exp 1 < |t| := by
          have h_e_bound : Real.exp 1 < 3 := by
                                                          
            simpa using lem_three_gt_e
          linarith [ht]
                                                                  
        have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (le_of_lt h_t_gt_e)
      have h_log_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
      rw [pow_two]
      exact le_mul_of_one_le_right (le_of_lt h_log_pos) h_log_ge_one

    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ))‖ + C_1 * Real.log |t| := h_triangle
      _ ≤ (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖s - ρ‖) + C_1 * Real.log |t| := by
          apply add_le_add_left h_triangle_ineq
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t| := by
          apply add_le_add_left h_sum_bound
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t|^2 := by
                                                    
          have h_c1_nonneg : 0 ≤ C_1 := le_of_lt (lt_trans zero_lt_one hC_1_gt)
          exact add_le_add_right (mul_le_mul_of_nonneg_left h_log_sq_ge h_c1_nonneg) _
      _ = (C_4 + C_1) * Real.log |t|^2 := by ring
      _ = (C_1 + C_4) * Real.log |t|^2 := by ring

lemma lem_term_real_nonneg (n : ℕ) (σ : ℝ) (_hσ : 1 < σ) : ∃ r ≥ (0:ℝ), ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r : ℂ) := by
                                                     
  let r : ℝ := (ArithmeticFunction.vonMangoldt n) / ((n : ℝ) ^ σ)
  refine ⟨r, ?_, ?_⟩
  ·                                                                                      
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_nonneg : 0 ≤ (n : ℝ) ^ σ := by
      simpa using (Real.rpow_nonneg hbase_nonneg σ)
                                          
    have hv_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n) := by
      simp
    have : 0 ≤ (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ σ)⁻¹ :=
      mul_nonneg hv_nonneg (inv_nonneg.mpr hden_nonneg)
    simpa [r, div_eq_mul_inv] using this
  ·                                            
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_eq : (((n : ℝ) ^ σ : ℝ) : ℂ) = (n : ℂ) ^ (σ : ℂ) := by
      simpa using (Complex.ofReal_cpow (x := (n : ℝ)) (hx := hbase_nonneg) (y := σ))
    calc
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ)))
          = ((ArithmeticFunction.vonMangoldt n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) := by
              simp [hden_eq.symm]
      _ = (((ArithmeticFunction.vonMangoldt n : ℝ) / ((n : ℝ) ^ σ)) : ℝ) := by
              simp
      _ = (r : ℂ) := by rfl

lemma lem_norm_logDeriv_le_tsum (s : ℂ) (hs : 1 < s.re) :
  ‖deriv riemannZeta s / riemannZeta s‖ ≤ ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := by
  classical
                                                      
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                                                  
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) := by
    simpa [f] using! (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs)
                                                                                
  have hsum_norm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    (summable_norm_iff).mpr hsum_term
                                                                            
  have hEq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s := by
    simpa [f] using! (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs)
                                                                                         
  have hpoint : (fun n : ℕ => ‖LSeries.term f s n‖)
                = (fun n : ℕ => ‖f n / ((n : ℂ) ^ s)‖) := by
    funext n
    by_cases h0 : n = 0
    ·                              
      subst h0
                                                
      have hf0r : ArithmeticFunction.vonMangoldt 0 = 0 := by
        simp
      have hf0 : f 0 = 0 := by simp [f, hf0r]
      simp [LSeries.term, f, hf0]
    ·                                              
      simp [LSeries.term, f, h0]
                                                      
  calc
    ‖deriv riemannZeta s / riemannZeta s‖
        = ‖- deriv riemannZeta s / riemannZeta s‖ := by simp [norm_neg]
    _ = ‖∑' n : ℕ, LSeries.term f s n‖ := by simp [hEq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ :=
          norm_tsum_le_tsum_norm (f := fun n : ℕ => LSeries.term f s n) hsum_norm
    _ = ∑' n : ℕ, ‖f n / ((n : ℂ) ^ s)‖ := by simp [hpoint]
    _ = ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := rfl

lemma lem_tsum_norm_vonMangoldt_depends_on_Re_cast (s : ℂ) (σ : ℝ)
  (hσ : σ = s.re) (hs : 1 < s.re) :
  (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
    = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
                       
  have hre_ne_zero : s.re ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  have hσ_ne_zero : σ ≠ 0 := by
    have : 0 < σ := by simpa [hσ] using (lt_trans zero_lt_one hs)
    exact ne_of_gt this
                                                                                
  have hterm : (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
      = (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n
                                                             
    have hden_s : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n hre_ne_zero
    have hden_σ : ‖(n : ℂ) ^ (σ : ℂ)‖ = (n : ℝ) ^ (σ : ℂ).re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa [Complex.ofReal_re] using hσ_ne_zero)
    calc
      ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖
          = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ s‖ := by simp
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ s.re) := by
            simp [hden_s, Complex.norm_real]
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ σ) := by simp [hσ]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ (σ : ℂ)‖ := by
            simp [hden_σ, Complex.ofReal_re, Complex.norm_real]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖ := by simp
  simpa using congrArg (fun f : ℕ → ℝ => ∑' n, f n) hterm

lemma helper_norm_neg_logDeriv_eq_tsum_norm (σ : ℝ) (hσ : 1 < σ) :
  ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ =
    (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
  classical
                                  
  let s : ℂ := (σ : ℂ)
                                                                             
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                                                     
  let u : ℕ → ℂ := fun n => LSeries.term f s n
                                                   
  have hs_re : 1 < s.re := by simpa using! hσ
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) := by
    simpa [f] using! (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs_re)
                       
  have hsum_u : Summable u := hsum_term
                                                        
  have hL_eq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs_re)
  have hsum_eq : (∑' n, u n) = - deriv riemannZeta s / riemannZeta s := by
    simpa [u] using hL_eq

  have hterm_as_div : ∀ n,
      u n = ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) := by
    intro n; by_cases h0 : n = 0
    ·         
      subst h0; simp [u, LSeries.term, f, s]
    ·         
      simp [u, LSeries.term, f, s, h0]
                                                           
  let r : ℕ → ℝ := fun n => Classical.choose (lem_term_real_nonneg n σ hσ)
  have hr_nonneg : ∀ n, 0 ≤ r n := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ hσ)).1
  have hr_cast : ∀ n,
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r n : ℂ) := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ hσ)).2
  have hr_eq' : ∀ n, u n = (r n : ℂ) := by
    intro n; simpa [hterm_as_div n] using (hr_cast n)
                                       
  have hsum_rc : Summable (fun n => (r n : ℂ)) := by
    simpa [u, hr_eq'] using hsum_u
  have hsum_r : Summable r := (Complex.summable_ofReal).1 hsum_rc
                                                         
  have hsum_u_as_real : (∑' n, u n) = ((∑' n, r n) : ℝ) := by
    have hru : (fun n => (r n : ℂ)) = u := by
      funext n; symm; exact hr_eq' n
    have := (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := r))

    simpa [hru] using this.symm
                                                             
  have hpoint_norm : (fun n : ℕ => ‖u n‖)
        = (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n; by_cases h0 : n = 0
    · subst h0; simp [u, LSeries.term, f, s]
    · simp [u, LSeries.term, f, s, h0]
  have hnorm_fun : (fun n : ℕ => ‖u n‖) = r := by
    funext n; simp [hr_eq' n, Complex.norm_real, abs_of_nonneg (hr_nonneg n)]
  have hsum_norm : Summable (fun n : ℕ => ‖u n‖) := by
    simpa [hnorm_fun] using hsum_r
                                                        
  have hineq : ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ :=
    norm_tsum_le_tsum_norm (f := u) hsum_norm
                                                  
  set S : ℝ := ∑' n, r n
  have hS_le : ‖((S : ℝ) : ℂ)‖ ≤ S := by
    simpa [S, hsum_u_as_real, hnorm_fun] using hineq
                              
  have hS_nonneg : 0 ≤ S := by
    have habs_le : |S| ≤ S := by simpa [Complex.norm_real] using hS_le
    exact (abs_nonneg S).trans habs_le
                                                
  have h_left : ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
      = ‖∑' n, u n‖ := by
    have : - deriv riemannZeta s / riemannZeta s = ∑' n, u n := by simpa [hsum_u_as_real] using hsum_eq.symm
    simp [s, this]
  have h_mid : ‖∑' n, u n‖ = S := by
                                               
    have : ‖((S : ℝ) : ℂ)‖ = S := by simp [Complex.norm_real, abs_of_nonneg hS_nonneg]
    simpa [S, hsum_u_as_real] using this
  have h_right : (∑' n : ℕ, ‖u n‖) = S := by simp [S, hnorm_fun]
                                            
  calc
    ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = ‖∑' n, u n‖ := h_left
    _ = S := h_mid
    _ = (∑' n : ℕ, ‖u n‖) := h_right.symm
    _ = (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
          simp [hpoint_norm]

theorem lem_zetacenterbd :
  ∀ t : ℝ,
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤
      ‖deriv riemannZeta σ / riemannZeta σ‖ := by
  intro t σ hσge
                   
  set s : ℂ := Complex.mk σ t
                                                  
  have hs : 1 < s.re := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
  have hσgt1 : 1 < σ := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
                                                           
  have h_le_sum := lem_norm_logDeriv_le_tsum s hs
  have h1 : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := by
    simpa [norm_div, Complex.norm_real] using h_le_sum
                                                                                       
  have h_dep :
      (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
                    
    have hre : σ = s.re := by simp [s]
    simpa using (lem_tsum_norm_vonMangoldt_depends_on_Re_cast s σ hre hs)
  have h_dep_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖)
        = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := by
    simpa [norm_div, Complex.norm_real] using h_dep
                                                            
  have h_sum_eq_norm :
      ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) :=
    helper_norm_neg_logDeriv_eq_tsum_norm σ hσgt1
  have h_sum_eq_norm_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖)
        = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    simpa [norm_div, Complex.norm_real] using h_sum_eq_norm.symm
                                      
  have h_main : ‖deriv riemannZeta s / riemannZeta s‖ ≤ ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    calc
      ‖deriv riemannZeta s / riemannZeta s‖
          ≤ (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := h1
      _ = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := h_dep_ratio
      _ = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := h_sum_eq_norm_ratio
                                                          
  simpa [s, norm_neg] using h_main

lemma lem_logDerivZetalogt32 :
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C := by
                                                        
  obtain ⟨C0, hC0_gt1, hC0_bound⟩ := Z0bound_const
                                            
  refine ⟨C0 + 2, by linarith, ?_⟩
  intro t ht σ hσ
                                                   
  have h_center := lem_zetacenterbd t σ hσ
                                  
  set δ : ℝ := σ - 1
  have hδ_pos : 0 < δ := by linarith [hσ]
  have hδ_ge_half : (1 / 2 : ℝ) ≤ δ := by linarith [hσ]
                                                     
  have hZ0 := hC0_bound δ hδ_pos
                                                                                   
  have h_tri : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤
      ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ + ‖(1 / (δ : ℂ))‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_add_le (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) (1 / (δ : ℂ)))
                                        
  have h_norm_div_le_two : ‖(1 / (δ : ℂ))‖ ≤ 2 := by
                                                          
    have hnorm_div : ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      simp
    have hnorm_ofReal : ‖(δ : ℂ)‖ = |δ| := by
      simp
                                        
    have h_abs_ge : (1 / 2 : ℝ) ≤ |δ| := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [abs_of_nonneg hδ_nonneg] using hδ_ge_half
    have hhalfpos : (0 : ℝ) < 1 / 2 := by norm_num
    have hone_div_abs_le_two : 1 / |δ| ≤ 2 := by
      simpa using (one_div_le_one_div_of_le hhalfpos h_abs_ge)
                                             
    have : 1 / ‖(δ : ℂ)‖ ≤ 2 := by simpa [hnorm_ofReal] using hone_div_abs_le_two
                                      
    have hnorm_div' : ‖(1 / (δ : ℂ))‖ = 1 / ‖(δ : ℂ)‖ := by
      simp
    simpa [hnorm_div'] using this
                                                                                           
  have h_real_axis_bound : ‖logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 := by
    have h1 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + ‖(1 / (δ : ℂ))‖ :=
      le_trans h_tri (add_le_add_left hZ0 _)
    have h2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 :=
      le_trans h1 (add_le_add_right h_norm_div_le_two _)
    simpa [norm_neg] using h2
                           
  have hσ_real : (1 : ℝ) + δ = σ := by
    simp [δ, sub_eq_add_neg, add_left_comm]
  have hσ_eq : (1 : ℂ) + δ = (σ : ℂ) := by
    have : ((1 + δ : ℝ) : ℂ) = (σ : ℂ) := by simpa using congrArg Complex.ofReal hσ_real
    simpa [Complex.ofReal_add] using this
  have hR_bound : ‖deriv riemannZeta σ / riemannZeta σ‖ ≤ C0 + 2 := by
                                                    
    simpa [logDerivZeta, hσ_eq] using h_real_axis_bound
                                    
  exact le_trans h_center hR_bound

theorem thm_final_result :
  ∃ A : ℝ, A > 0 ∧ A < 1 ∧
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 1 - A / Real.log (abs t + 2) →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C * (Real.log (abs t)) ^ 2 := by
                                                                                          
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := lem_logDerivZetalogt0
  obtain ⟨C₃₂, hC₃₂_pos, hC₃₂⟩ := lem_logDerivZetalogt32

  use zerofree_constant / 20

  constructor
  ·               
    apply div_pos zerofree_constant_pos
    norm_num

  constructor
  ·               
    rw [div_lt_one (by norm_num : (0 : ℝ) < 20)]
                                          
    have h1 : zerofree_constant < 1 := zerofree_constant_lt_one
    linarith

  use max C₀ C₃₂

  constructor
  ·               
    exact lt_max_of_lt_left hC₀_pos

  ·              
    intro t ht σ hσ

    have h_eq : zerofree_constant / 20 / Real.log (abs t + 2) = deltaz_t t := by
      unfold deltaz_t deltaz
      simp

    have hσ' : σ ≥ 1 - deltaz_t t := by
      rw [← h_eq]
      exact hσ

    by_cases h : σ ≥ 3/2
    ·                                            
      have bound := hC₃₂ t ht σ h
      have hC_le : C₃₂ ≤ max C₀ C₃₂ := le_max_right _ _
                                                      
      have hlog_ge_one : 1 ≤ Real.log (abs t) := by
        have h_ge : Real.exp 1 ≤ abs t := by
                                                     
          have he_lt_3 : Real.exp 1 < 3 := lem_three_gt_e                           
          linarith [ht, abs_nonneg t]
        exact (Real.le_log_iff_exp_le (by linarith [abs_nonneg t])).2 h_ge
      have h_one_le_sq : 1 ≤ (Real.log (abs t)) ^ 2 := by
        have h_sq : (Real.log (abs t)) ^ 2 = Real.log (abs t) * Real.log (abs t) := by
          rw [pow_two]
        rw [h_sq]
        have h_mul : 1 * 1 ≤ Real.log (abs t) * Real.log (abs t) :=
          mul_self_le_mul_self (zero_le_one) hlog_ge_one
        simpa using h_mul
      have h_pos : 0 < C₃₂ := lt_trans zero_lt_one hC₃₂_pos
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₃₂ := bound
        _ = C₃₂ * 1 := by rw [mul_one]
        _ ≤ C₃₂ * (Real.log (abs t)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left h_one_le_sq (le_of_lt h_pos)
        _ ≤ max C₀ C₃₂ * (Real.log (abs t)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)

    ·                                           
      push Not at h
      have h_conditions : 1 - deltaz_t t ≤ σ ∧ σ ≤ 3/2 ∧ t = t := by
        exact ⟨hσ', le_of_lt h, rfl⟩
      have bound := hC₀ t ht ⟨σ, t⟩ h_conditions
      have hC_le : C₀ ≤ max C₀ C₃₂ := le_max_left _ _
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₀ * Real.log |t| ^ 2 := bound
        _ ≤ max C₀ C₃₂ * Real.log |t| ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)

lemma ZetaZeroFree_p :
    ∃ (A : ℝ) (_ : A ∈ Set.Ioc 0 (1 / 2)),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Set.Ico (1 - A / Real.log |t| ^ 1) 1),
    riemannZeta (σ + t * Complex.I) ≠ 0 := by
                                                                             
  obtain ⟨c, hc_pos, hc_lt_one, hbound⟩ := zerofree
                                               
  let A0 : ℝ := min (1 / 2 : ℝ) (c / 2)
  let A : ℝ := min A0 ((1 / 4 : ℝ) * Real.log 3)
  have hA_pos : 0 < A := by
    have h1 : 0 < (1 / 2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc_pos this
    have hA0pos : 0 < A0 := lt_min_iff.mpr ⟨h1, h2⟩
    have hlog3pos : 0 < Real.log (3 : ℝ) :=
      (Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 3)).2 (by norm_num)
    have h3 : 0 < (1 / 4 : ℝ) * Real.log 3 := by
      exact mul_pos (by norm_num) hlog3pos
    exact lt_min_iff.mpr ⟨hA0pos, h3⟩
  have hA_le_half : A ≤ 1/2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_left _ _)
  have hA_le_c2 : A ≤ c / 2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_right _ _)
  have hA_le_log3quarter : A ≤ (1 / 4 : ℝ) * Real.log 3 := min_le_right _ _
  refine ⟨A, ?_, ?_⟩
  · exact ⟨hA_pos, hA_le_half⟩
  · intro σ t htgt3 hσI hzero
                        
    set L := Real.log |t| with hLdef
    set Lp := Real.log (|t| + 2) with hLpdef
    have hpos_abs : 0 ≤ |t| := abs_nonneg t
    have hLpos : 0 < L := (Real.log_pos_iff hpos_abs).2 (lt_trans (by norm_num) htgt3)
    have hLp_pos_arg : 0 < |t| + 2 := by linarith
    have hLp_pos : 0 < Lp := (Real.log_pos_iff (le_of_lt hLp_pos_arg)).2 (by linarith)
                                      
    have hlog3_le_L : Real.log 3 ≤ L := by
      have h3pos : 0 < (3 : ℝ) := by norm_num
      have : (3 : ℝ) ≤ |t| := le_of_lt htgt3
      simpa [hLdef] using Real.log_le_log h3pos this
                                  
    have hquarter_ratio_le : ((1 / 4 : ℝ) * Real.log 3) / L ≤ (1 / 4 : ℝ) := by
      have h := div_le_div_of_nonneg_right hlog3_le_L (le_of_lt hLpos)
      have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/4)
      have hne : L ≠ 0 := ne_of_gt hLpos
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne] using h'
                          
    have hA_over_le_quarter : A / L ≤ (1 / 4 : ℝ) := by
      have := div_le_div_of_nonneg_right hA_le_log3quarter (le_of_lt hLpos)
      exact this.trans hquarter_ratio_le
                                   
    have hlow : 1 - A / L ≤ σ := by simpa [hLdef, pow_one] using hσI.1
    have hσ_ge_34 : (3 / 4 : ℝ) ≤ σ := by
      have : (3 / 4 : ℝ) ≤ 1 - A / L := by linarith
      exact this.trans hlow
    have hσ_pos : 0 < σ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3/4 : ℝ)) hσ_ge_34
    have hσ_lt_one : σ < 1 := hσI.2
                   
    have hlog_lt : Lp < 2 * L := by
      have h1 : 0 < |t| - 2 := by linarith
      have h2 : 0 < |t| + 1 := by linarith
      have hprod_pos : 0 < (|t| - 2) * (|t| + 1) := mul_pos h1 h2
      have hpoly : |t| * |t| - (|t| + 2) = (|t| - 2) * (|t| + 1) := by ring
      have hlt : |t| + 2 < |t| * |t| := by
        calc
          |t| + 2 < |t| + 2 + (|t| - 2) * (|t| + 1) := by linarith [hprod_pos]
          _ = |t| * |t| := by rw [← hpoly]; ring
      have hposb : 0 < |t| + 2 := by linarith
      have hlog_lt' : Real.log (|t| + 2) < Real.log (|t| * |t|) := Real.log_lt_log hposb hlt
      have hlogmul : Real.log (|t| ^ 2) = 2 * Real.log |t| := Real.log_pow |t| 2
      calc
        Lp = Real.log (|t| + 2) := by simp [hLpdef]
        _ < Real.log (|t| * |t|) := hlog_lt'
        _ = Real.log (|t| ^ 2) := by simp [pow_two]
        _ = 2 * Real.log |t| := by simp
        _ = 2 * L := by simp [hLdef]
                                               
    have h_inv_comp : 1 / (2 * L) < 1 / Lp := one_div_lt_one_div_of_lt hLp_pos hlog_lt
    have hstep2 : (c / 2) / L < c / Lp := by
      have hcpos' : 0 < c := hc_pos
      have : c * (1 / (2 * L)) < c * (1 / Lp) := mul_lt_mul_of_pos_left h_inv_comp hcpos'
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
                                          
    have hstep1 : A / L ≤ (c / 2) / L := by
      have := div_le_div_of_nonneg_right hA_le_c2 (le_of_lt hLpos)
      simpa [div_eq_mul_inv] using this
    have hstrict_div : A / L < c / Lp := lt_of_le_of_lt hstep1 hstep2
                                                       
    have hσ_gt : 1 - c / Lp < σ := by
      have hneg' : - (c / Lp) < - (A / L) := by simpa [neg_div] using neg_lt_neg hstrict_div
      have : 1 - c / Lp < 1 - A / L := by simpa [sub_eq_add_neg] using! add_lt_add_right hneg' 1
      exact this.trans_le hlow
                                             
    let s : ℂ := Complex.mk σ t
    have hs_zero : riemannZeta s = 0 := by simpa [s, Complex.mk_eq_add_mul_I] using hzero
    have hs_in_zeroZ : s ∈ zeroZ := by simpa [zeroZ] using hs_zero
    have hpre : s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1 := by
      refine ⟨hs_in_zeroZ, ?_, ?_⟩
      · simpa [s] using hσ_pos
      · simpa [s] using hσ_lt_one
    have him_bound : 2 < |s.im| := by
      have : 2 < |t| := lt_trans (by norm_num) htgt3
      simpa [s] using this
    have hbound_applied : s.re ≤ 1 - c / Real.log (abs s.im + 2) := hbound s hpre him_bound
    have hle : σ ≤ 1 - c / Lp := by simpa [s, hLpdef] using hbound_applied
    have hcontr : σ < σ := lt_of_le_of_lt hle hσ_gt
    exact (lt_irrefl _ : ¬ σ < σ) hcontr

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real
lemma LogDerivZetaBndUnif2 :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 1)), ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      C * Real.log |t| ^ 2 := by
  classical
  obtain ⟨c, hc, hc2, K, hK, hfinal⟩ := thm_final_result
                     
  let A : ℝ := min (1/2 : ℝ) (c / 2)
  have hApos : 0 < A := by
    have h1 : 0 < (1/2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc this
    exact (lt_min_iff).2 ⟨h1, h2⟩
  have hAle : A ≤ (1/2 : ℝ) := min_le_left _ _
  have hA_in : A ∈ Ioc 0 (1/2) := ⟨hApos, hAle⟩
  let C : ℝ := K
  have hCpos : 0 < C := by
    have hKpos : 0 < K := lt_trans (by norm_num : (0 : ℝ) < 1) hK
    exact hKpos
  refine ⟨A, hA_in, C, hCpos, ?_⟩
  intro σ t htgt3 hσI
                      
  let x := |t|
  have hxpos : 0 ≤ x := abs_nonneg t
  have hxgt3 : 3 < x := htgt3
  let L := Real.log x
  let L' := Real.log (x + 2)
  have hLpos : 0 < L := (Real.log_pos_iff hxpos).2 (lt_trans (by norm_num) hxgt3)
  have hL'pos : 0 < L' :=
    (Real.log_pos_iff (by linarith : 0 ≤ x + 2)).2 (by linarith [hxpos, hxgt3])
                                             
  have hσ_ge : 1 - A / L ≤ σ := by simpa [pow_one, L, x] using hσI
                 
  have hprod_pos : 0 < (x - 2) * (x + 1) := by
    have hxgt2 : (2 : ℝ) < x := lt_trans (by norm_num) hxgt3
    exact mul_pos (sub_pos.mpr hxgt2) (add_pos_of_nonneg_of_pos hxpos (by norm_num))
  have hdiff_pos : 0 < x ^ 2 - (x + 2) := by
    have hpoly : x ^ 2 - (x + 2) = (x - 2) * (x + 1) := by ring
    simpa [hpoly] using hprod_pos
  have hlt_sq : x + 2 < x ^ 2 := by linarith
  have hlog_lt : L' < Real.log (x ^ 2) :=
    Real.log_lt_log (by linarith : 0 < x + 2) hlt_sq
  have hlog_pow : Real.log (x ^ 2) = 2 * L := by
    simp [L]
  have hL'_lt_2L : L' < 2 * L := by simpa [L', hlog_pow]
    using hlog_lt
                                       
  have hA_le_c2 : A ≤ c / 2 := min_le_right _ _
  have hstep0 : A / L ≤ (c / 2) / L :=
    div_le_div_of_nonneg_right hA_le_c2 (le_of_lt hLpos)
  have hrecip : 1 / (2 * L) < 1 / L' :=
    one_div_lt_one_div_of_lt hL'pos hL'_lt_2L
  have hmul : c * (1 / (2 * L)) < c * (1 / L') :=
    mul_lt_mul_of_pos_left hrecip hc
  have hstep2 : (c / 2) / L < c / L' := by
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hmul
  have hineq : A / L < c / L' := lt_of_le_of_lt hstep0 hstep2
  have hσ_gt : σ > 1 - c / L' := by
    have : 1 - c / L' < 1 - A / L := by linarith [hineq]
    exact lt_of_lt_of_le this hσ_ge
                                                 
  have hmain' : ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      K * (Real.log |t|) ^ 2 := by
    have h_eq : σ + t * Complex.I = Complex.mk σ t := by
      rw [Complex.mk_eq_add_mul_I]
    rw [h_eq]
    have hσ_ge_required : σ ≥ 1 - c / Real.log (abs t + 2) := by
      have h_abs_eq : abs t = |t| := by simp
      rw [h_abs_eq]
      exact le_of_lt hσ_gt
    exact hfinal t htgt3 σ hσ_ge_required
                                                  
  simpa [C, L, x] using hmain'

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_ZetaZeroFree
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

open _root_.Complex Topology _root_.Filter Interval _root_.Set Asymptotics
local notation (name := riemannzeta') "ζ" => riemannZeta
local notation (name := derivriemannzeta') "ζ'" => deriv riemannZeta

local notation "I" => Complex.I

lemma ZetaNoZerosInBox' (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  by_contra h
  push Not at h

  have hn (n : ℕ) := h (σ := 1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra hσn
    push Not at hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n + 1)) atTop (𝓝 1) := by
      simpa using! (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hσ'_ge hσ'_le

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by valid, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert (preTransparency := .instances) hζ (subseq n) using 3
    all_goals try with_reducible_and_instances rfl
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      have hprod : Tendsto (fun s : ℂ => ‖(s - 1) * ζ s‖) (𝓝[≠] 1) (𝓝 1) := by
        simpa only [norm_one] using! riemannZeta_residue_one.norm
      have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] 1) (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hdist : Tendsto (fun s : ℂ => ‖s - 1‖) (𝓝[≠] 1) (𝓝 0) := by
        simpa only [sub_self, norm_zero] using! (hid.sub_const 1).norm
      filter_upwards [hprod.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
        hdist.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with s hp hs
      by_contra h
      have hlt : ‖ζ s‖ < 1 := lt_of_not_ge h
      have hm := mul_le_mul_of_nonneg_left hlt.le (norm_nonneg (s - 1))
      rw [norm_mul] at hp
      rw [mul_one] at hm
      linarith

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have hpoint : (1 + Complex.I * t₀ : ℂ) ≠ 1 := by
        intro heq
        have him := congrArg Complex.im heq
        have htzero : t₀ = 0 := by simpa using him
        exact ht₀ htzero
      have hcont := (differentiableAt_riemannZeta hpoint).continuousAt
      have hlim : Tendsto (fun n : ℕ => ζ (σ' (subseq n) + I * t (subseq n))) atTop
          (𝓝 (ζ (1 + I * t₀))) := by
        simpa only [Function.comp_def] using!
          hcont.tendsto.comp (ToOneT0.mono_right nhdsWithin_le_nhds)
      have hfun : (fun n : ℕ => ζ (σ' (subseq n) + I * t (subseq n))) = (fun _ => 0) :=
        funext this
      rw [hfun] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero

theorem LogDerivZetaHolcLargeT' :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree_p
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox' 3
  let A₀ := min A ((1 - σ₁) * Real.log 3 ^ 1)
  refine ⟨A₀, ?_, ?_⟩
  · constructor
    · apply lt_min A_inter.1
      bound
    · exact le_trans (min_le_left _ _) A_inter.2
  intro T hT
  apply LogDerivZetaHoloOn
  · exact notMem_sdiff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ 1 := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1

  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ 1 := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ 1 := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ 1)) / Real.log 3 ^ 1:= by
        gcongr
        apply min_le_right
      _ = _ := by field_simp <;> ring

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT5_Strong
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

lemma LogDerivZetaBoundedAndHolo_jd_oai : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by

  obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd2⟩ := LogDerivZetaBndUnif2
  obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT'
  refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  ·                                                                                  
    intro σ t ht hσ
    have hσ' : σ ∈ Ici (1 - A₁ / Real.log |t| ^ 1) := by

      have hAle : min A₁ A₂ ≤ A₁ := min_le_left _ _
      have hlogpos : 0 < Real.log |t| := by
                               
        exact Real.log_pos (lt_trans (by norm_num) ht)
      have := sub_le_sub_left
        (div_le_div_of_nonneg_right (show min A₁ A₂ ≤ A₁ from hAle) (le_of_lt hlogpos)) 1
                                     
      have hthr : 1 - A₁ / Real.log |t| ^ 1 ≤ 1 - (min A₁ A₂) / Real.log |t| ^ 1 := by
        simpa [pow_one] using this
                                           
      have : σ ∈ Ici (1 - (min A₁ A₂) / Real.log |t| ^ 1) := by
        simpa [pow_one] using hσ
      exact le_trans hthr (mem_Ici.mp this)
                                                                           
    have hmain := zeta_bnd2 σ t ht (by simpa [pow_one] using hσ')
    have hlog_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                                                              
      have hpos : 0 < |t| := lt_trans (by norm_num) ht
      have hle : Real.exp 1 ≤ |t| := by
        have : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
        exact this.trans (le_of_lt ht)
      have := Real.log_le_log (Real.exp_pos 1) hle
      simpa [Real.log_exp] using this
    have hpow : Real.log |t| ^ (2 : ℕ) ≤ Real.log |t| ^ (9 : ℕ) := by
      exact pow_le_pow_right₀ hlog_ge_one (by decide : (2 : ℕ) ≤ 9)
                                   
    have : C * Real.log |t| ^ (2 : ℕ) ≤ C * Real.log |t| ^ (9 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt C_pos)
    exact (le_trans hmain this)
  ·                                                                    
    intro T hT
                                                                           
    have hsubset :
        ((Icc ((1 : ℝ) - min A₁ A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) ⊆
        ((Icc ((1 : ℝ) - A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) := by
      intro s hs
      rcases hs with ⟨hs_box, hs_ne⟩
      rcases hs_box with ⟨hre, him⟩
      rcases hre with ⟨hre_left, hre_right⟩
                                     
      constructor
      ·                                                     
        constructor
        ·                                              
          constructor
          ·                                  
            have hAle : min A₁ A₂ ≤ A₂ := min_le_right _ _
            have hlogpos : 0 < Real.log T := by
              have hT' : 1 < T := by linarith
              exact Real.log_pos hT'
            have := sub_le_sub_left
              (div_le_div_of_nonneg_right hAle (le_of_lt hlogpos)) 1
            have hthr : 1 - A₂ / Real.log T ^ 1 ≤ 1 - (min A₁ A₂) / Real.log T ^ 1 := by
              simpa [pow_one] using this
            exact le_trans hthr hre_left
          · exact hre_right
        · exact him
      · exact hs_ne
    exact (holo T hT).mono hsubset

open _root_.Filter Topology

end Erdos970
end

theorem solution : type_of% @Erdos970.LogDerivZetaBoundedAndHolo_jd_oai := @Erdos970.LogDerivZetaBoundedAndHolo_jd_oai
