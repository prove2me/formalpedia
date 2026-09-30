-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.coordinating_target_iff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:37:32.283085+00:00
-- url     : https://prove2.me/submissions/a329abec-8f04-4152-97b0-2735441bd3cd

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
open MeasureTheory Set
open FalseFailureReturns.TargetRebate
private lemma shortfall_formula (β ρ T : ℝ) (hβ : 0 < β) (hρ : 0 < ρ)
    (hT0 : 0 ≤ T) (hT : T ≤ 2*β/ρ) : expShortfall β ρ T = T^2*ρ/(4*β) := by
  let B := 2*β/ρ
  have hB : 0 < B := by dsimp [B]; positivity
  have hf : Continuous (fun x : ℝ => max (T-x) 0) := by fun_prop
  have hi : ∫ x in Icc (0:ℝ) B, max (T-x) 0 = T^2/2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hB.le]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 T)
      (hf.intervalIntegrable T B)]
    have hleft : ∫ x in (0:ℝ)..T, max (T-x) 0 = ∫ x in (0:ℝ)..T, T-x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hT0] at hx
      exact max_eq_left (by linarith [hx.2])
    have hright : ∫ x in T..B, max (T-x) 0 = 0 := by
      calc
        _ = ∫ x in T..B, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hT] at hx
          exact max_eq_right (by linarith [hx.1])
        _ = 0 := by simp
    have hc : IntervalIntegrable (fun _ : ℝ => T) volume 0 T := continuous_const.intervalIntegrable _ _
    have hid : IntervalIntegrable (fun x : ℝ => x) volume 0 T := continuous_id.intervalIntegrable _ _
    rw [hleft, hright, add_zero, intervalIntegral.integral_sub hc hid,
      intervalIntegral.integral_const, integral_id]
    ring
  unfold expShortfall uniformLaw ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal hB.le, smul_eq_mul]
  change B⁻¹ * (∫ x in Icc (0:ℝ) B, max (T-x) 0) = _
  rw [hi]
  dsimp [B]
  field_simp <;> ring

open Filter Topology
private lemma rebate_derivative (P : Params) (T u r : ℝ) (hβ : 0 < P.β) (hr : 0 < r)
    (hT0 : 0 ≤ T) (hT : T < 2*P.β/r) :
    HasDerivAt (rebateRetailerProfit P T u)
      (T^2*u/(4*P.β)-P.a*r+P.Rr*P.β/r^2) r := by
  have he : rebateRetailerProfit P T u =ᶠ[𝓝 r]
      (fun x : ℝ => T^2*u*x/(4*P.β)-P.a*x^2/2+P.Rr*P.β*(1-1/x)) := by
    have hmul : T*r < 2*P.β := (lt_div_iff₀ hr).mp hT
    have hc : Continuous (fun x : ℝ => 2*P.β-T*x) := by fun_prop
    filter_upwards [eventually_gt_nhds hr, hc.continuousAt.eventually (eventually_gt_nhds (by linarith : 0 < 2*P.β-T*r))] with x hx htx
    rw [rebateRetailerProfit, shortfall_formula _ _ _ hβ hx hT0 ((le_div_iff₀ hx).mpr (by linarith))]
    ring
  have hd := (((hasDerivAt_id r).const_mul (T^2*u)).div_const (4*P.β)).sub
    ((((hasDerivAt_id r).pow 2).const_mul P.a).div_const 2)
  have hi := ((((hasDerivAt_const r (1:ℝ)).div (hasDerivAt_id r) hr.ne').const_sub 1).const_mul (P.Rr*P.β))
  have hd' : HasDerivAt
      (fun x : ℝ => T^2*u*x/(4*P.β)-P.a*x^2/2+P.Rr*P.β*(1-1/x))
      (T^2*u/(4*P.β)-P.a*r+P.Rr*P.β/r^2) r := by
    convert! hd.add hi using 1 <;> first | rfl | (funext x; rfl) | (dsimp; ring)
  exact hd'.congr_of_eventuallyEq he
private lemma rebate_foc (P : Params) (T u r : ℝ) (hβ : 0 < P.β)
    (hT0 : 0 ≤ T) (hr : 1 < r)
    (hmax : IsMaxOn (rebateRetailerProfit P T u) (Set.Ici 1) r)
    (hT : T < 2*P.β/r) :
    T^2*u*r^2-4*P.a*P.β*r^3+4*P.Rr*P.β^2=0 := by
  have hd := rebate_derivative P T u r hβ (by linarith) hT0 hT
  have hm : IsLocalMax (rebateRetailerProfit P T u) r := hmax.isLocalMax (Ici_mem_nhds hr)
  have hz : T^2*u/(4*P.β)-P.a*r+P.Rr*P.β/r^2=0 := hd.deriv.symm.trans hm.deriv_eq_zero
  have hr0 : r ≠ 0 := by linarith
  field_simp [hr0, hβ.ne'] at hz
  nlinarith [hz]

private lemma coord_gt (P : Params) (ha : 0 < P.a)
    (hint : P.a < (P.Mm+P.Rr)*P.β) : 1 < coordEffort P := by
  apply Real.one_lt_rpow _ (by norm_num)
  rw [div_mul_eq_mul_div, one_lt_div ha]
  exact hint
private lemma coord_cube (P : Params) (ha : 0 < P.a) (hβ : 0 < P.β)
    (hM : 0 < P.Mm) (hR : 0 < P.Rr) :
    P.a * coordEffort P ^ 3 = (P.Mm+P.Rr)*P.β := by
  unfold coordEffort
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num
  field_simp
private lemma coord_charge (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm+P.Rr)*P.β) (hT : 0 < T)
    (hTlt : T < 2*P.β/coordEffort P) (hcoord : Coordinates P T u) :
    u*expShortfall P.β (coordEffort P) T = P.Mm*P.β/coordEffort P := by
  have hc := coord_gt P ha hint
  have hcpos : 0 < coordEffort P := by linarith
  have hcb := coord_cube P ha hβ hM hR
  have hcb' := congrArg (fun x : ℝ => 4*P.β*x) hcb
  have hf := rebate_foc P T u (coordEffort P) hβ hT.le hc hcoord hTlt
  rw [shortfall_formula _ _ _ hβ hcpos hT.le hTlt.le]
  field_simp [hcpos.ne',hβ.ne']
  nlinarith [hcb',hf]
private lemma manufacturer_at_coord (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm+P.Rr)*P.β) (hT : 0 < T)
    (hTlt : T < 2*P.β/coordEffort P) (hcoord : Coordinates P T u) :
    rebateManufProfit P T u (coordEffort P) = P.Mm*P.β*((coordEffort P-2)/coordEffort P) := by
  rw [rebateManufProfit,coord_charge P T u ha hβ hM hR hint hT hTlt hcoord]
  have hcpos : 0 < coordEffort P := lt_trans zero_lt_one (coord_gt P ha hint)
  field_simp [hcpos.ne'] <;> ring
private lemma retailer_at_coord (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm+P.Rr)*P.β) (hT : 0 < T)
    (hTlt : T < 2*P.β/coordEffort P) (hcoord : Coordinates P T u) :
    rebateRetailerProfit P T u (coordEffort P) =
      P.β*(P.Mm-3*P.Rr)/(2*coordEffort P)+P.Rr*P.β := by
  rw [rebateRetailerProfit,coord_charge P T u ha hβ hM hR hint hT hTlt hcoord]
  have hcpos : 0 < coordEffort P := lt_trans zero_lt_one (coord_gt P ha hint)
  have hcb := coord_cube P ha hβ hM hR
  field_simp [hcpos.ne']
  nlinarith [hcb]
private lemma retailer_gain (P : Params) (T u : ℝ) (hu : 0 ≤ u)
    (hcoord : Coordinates P T u) :
    retailerProfit P (decentrEffort P) ≤ rebateRetailerProfit P T u (coordEffort P) := by
  have hd : decentrEffort P ∈ Ici (1:ℝ) := by
    simp only [Set.mem_Ici, decentrEffort]
    exact le_max_right _ _
  have hh := hcoord hd
  have hn : 0 ≤ expShortfall P.β (decentrEffort P) T := integral_nonneg (fun x => le_max_right _ _)
  have hu' := mul_nonneg hu hn
  dsimp [rebateRetailerProfit,retailerProfit] at hh ⊢
  linarith

private lemma shortfall_above (β ρ T : ℝ) (hβ : 0 < β) (hρ : 0 < ρ)
    (hT : 2*β/ρ ≤ T) : expShortfall β ρ T = T-β/ρ := by
  let B := 2*β/ρ
  have hB : 0 < B := by dsimp [B]; positivity
  have hi : ∫ x in Icc (0:ℝ) B, max (T-x) 0 = T*B-B^2/2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hB.le]
    have he : ∫ x in (0:ℝ)..B, max (T-x) 0 = ∫ x in (0:ℝ)..B, T-x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hB.le] at hx
      exact max_eq_left (by linarith [hx.2])
    have hc : IntervalIntegrable (fun _ : ℝ => T) volume 0 B := continuous_const.intervalIntegrable _ _
    have hid : IntervalIntegrable (fun x : ℝ => x) volume 0 B := continuous_id.intervalIntegrable _ _
    rw [he,intervalIntegral.integral_sub hc hid,intervalIntegral.integral_const,integral_id]
    ring
  unfold expShortfall uniformLaw ProbabilityTheory.cond
  rw [integral_smul_measure,ENNReal.toReal_inv,Real.volume_Icc,sub_zero,
    ENNReal.toReal_ofReal hB.le,smul_eq_mul]
  change B⁻¹*(∫ x in Icc (0:ℝ) B, max (T-x) 0) = _
  rw [hi]
  dsimp [B]
  field_simp <;> ring
private lemma shortfall_upper (β ρ T : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hT : 0 ≤ T) :
    expShortfall β ρ T ≤ T^2*ρ/(4*β) := by
  by_cases h : T ≤ 2*β/ρ
  · exact (shortfall_formula β ρ T hβ hρ hT h).le
  · rw [shortfall_above β ρ T hβ hρ (le_of_not_ge h)]
    apply (le_div_iff₀ (by positivity : 0 < 4*β)).mpr
    have he : (T-β/ρ)*(4*β)*ρ = 4*T*β*ρ-4*β^2 := by field_simp <;> ring
    have hs := sq_nonneg (T*ρ-2*β)
    have hmul : (T-β/ρ)*(4*β)*ρ ≤ (T^2*ρ)*ρ := by rw [he]; nlinarith
    exact (mul_le_mul_iff_left₀ hρ).mp hmul
private lemma coordinate_of_charge (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm+P.Rr)*P.β) (hu : 0 < u) (hT : 0 < T)
    (hTlt : T < 2*P.β/coordEffort P)
    (hq : T^2*u*coordEffort P^2=4*P.Mm*P.β^2) : Coordinates P T u := by
  let C := coordEffort P
  have hcpos : 0 < C := lt_trans zero_lt_one (coord_gt P ha hint)
  have hcube := coord_cube P ha hβ hM hR
  have hcube' := congrArg (fun x : ℝ => 4*P.β*x) hcube
  have hz : T^2*u/(4*P.β)=P.a*C-P.Rr*P.β/C^2 := by
    field_simp [hcpos.ne',hβ.ne']
    dsimp [C] at *
    nlinarith [hq,hcube']
  let F := fun x : ℝ => T^2*u*x/(4*P.β)-P.a*x^2/2+P.Rr*P.β*(1-1/x)
  have heC : rebateRetailerProfit P T u C = F C := by
    rw [rebateRetailerProfit,shortfall_formula _ _ _ hβ hcpos hT.le hTlt.le]
    dsimp [F]
    ring
  intro y hy
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hybound := mul_le_mul_of_nonneg_left (shortfall_upper P.β y T hβ hypos hT.le) hu.le
  have heDiff : F C-F y=(y-C)^2*(P.a/2+P.Rr*P.β/(C^2*y)) := by
    dsimp [F]
    simp_rw [show T^2*u*C/(4*P.β)=(T^2*u/(4*P.β))*C by ring,
      show T^2*u*y/(4*P.β)=(T^2*u/(4*P.β))*y by ring, hz]
    field_simp [hcpos.ne',hypos.ne'] <;> ring
  have hn : 0 ≤ F C-F y := by rw [heDiff]; positivity
  change rebateRetailerProfit P T u y ≤ rebateRetailerProfit P T u C
  rw [heC]
  dsimp [F,rebateRetailerProfit] at *
  rw [show u*(T^2*y/(4*P.β))=T^2*u*y/(4*P.β) by ring] at hybound
  linarith

private noncomputable def targetFormula (P : Params) (u : ℝ) : ℝ :=
  2*P.β^((2:ℝ)/3)*P.a^((1:ℝ)/3)*P.Mm^((1:ℝ)/2) /
    (u^((1:ℝ)/2)*(P.Mm+P.Rr)^((1:ℝ)/3))
private lemma target_charge (P : Params) (u : ℝ) (ha : 0 < P.a) (hβ : 0 < P.β)
    (hM : 0 < P.Mm) (hR : 0 < P.Rr) (hu : 0 < u) :
    targetFormula P u ^ 2 * u * coordEffort P ^ 2 = 4*P.Mm*P.β^2 := by
  have hs : 0 < P.Mm+P.Rr := add_pos hM hR
  have hane := (Real.rpow_pos_of_pos ha ((1:ℝ)/3)).ne'
  have hsne := (Real.rpow_pos_of_pos hs ((1:ℝ)/3)).ne'
  have hune := (Real.rpow_pos_of_pos hu ((1:ℝ)/2)).ne'
  have hC : coordEffort P = ((P.Mm+P.Rr)^((1:ℝ)/3)/P.a^((1:ℝ)/3))*P.β^((1:ℝ)/3) := by
    rw [coordEffort,Real.mul_rpow (by positivity) hβ.le,Real.div_rpow hs.le ha.le]
  have hprod : P.β^((2:ℝ)/3)*P.β^((1:ℝ)/3)=P.β := by
    rw [← Real.rpow_add hβ]
    norm_num
  have hk : targetFormula P u*coordEffort P = 2*P.β*P.Mm^((1:ℝ)/2)/u^((1:ℝ)/2) := by
    calc
      _ = 2*(P.β^((2:ℝ)/3)*P.β^((1:ℝ)/3))*P.Mm^((1:ℝ)/2)/u^((1:ℝ)/2) := by
        rw [targetFormula,hC]
        field_simp [hane,hsne,hune] <;> ring
      _ = _ := by rw [hprod]
  have hmhalf : (P.Mm^((1:ℝ)/2))^2=P.Mm := by
    rw [← Real.rpow_mul_natCast hM.le]
    norm_num
  have huhalf : (u^((1:ℝ)/2))^2=u := by
    rw [← Real.rpow_mul_natCast hu.le]
    norm_num
  calc
    _ = (targetFormula P u*coordEffort P)^2*u := by ring
    _ = (2*P.β*P.Mm^((1:ℝ)/2)/u^((1:ℝ)/2))^2*u := by rw [hk]
    _ = _ := by
      rw [div_pow,mul_pow,mul_pow,hmhalf,huhalf]
      field_simp <;> ring

private lemma charge_from_coordinate (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm+P.Rr)*P.β) (hT : 0 < T)
    (hTlt : T < 2*P.β/coordEffort P) (hcoord : Coordinates P T u) :
    T^2*u*coordEffort P^2=4*P.Mm*P.β^2 := by
  have hcpos : 0 < coordEffort P := lt_trans zero_lt_one (coord_gt P ha hint)
  have he := coord_charge P T u ha hβ hM hR hint hT hTlt hcoord
  rw [shortfall_formula _ _ _ hβ hcpos hT.le hTlt.le] at he
  field_simp [hcpos.ne',hβ.ne'] at he
  nlinarith [he]

theorem solution (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) (hu : 0 < u) (hT : 0 < T) :
    (Coordinates P T u ∧ T < 2 * P.β / coordEffort P) ↔
      (T = 2 * P.β ^ ((2 : ℝ) / 3) * P.a ^ ((1 : ℝ) / 3) * P.Mm ^ ((1 : ℝ) / 2) /
          (u ^ ((1 : ℝ) / 2) * (P.Mm + P.Rr) ^ ((1 : ℝ) / 3)) ∧
        P.Mm < u) := by
  have hcpos : 0 < coordEffort P := lt_trans zero_lt_one (coord_gt P ha hint)
  have hkpos : 0 < targetFormula P u := by unfold targetFormula; positivity
  have hk := target_charge P u ha hβ hM hR hu
  have hpos : 0 < u*coordEffort P^2 := by positivity
  change (Coordinates P T u ∧ T < 2*P.β/coordEffort P) ↔ (T=targetFormula P u ∧ P.Mm<u)
  constructor
  · rintro ⟨hcoord,hTlt⟩
    have hq := charge_from_coordinate P T u ha hβ hM hR hint hT hTlt hcoord
    have hs : T^2=targetFormula P u^2 := by
      apply (mul_left_inj' hpos.ne').mp
      nlinarith [hq,hk]
    refine ⟨by nlinarith, ?_⟩
    have hTC := (lt_div_iff₀ hcpos).mp hTlt
    have hsTC : (T*coordEffort P)^2 < (2*P.β)^2 := by
      exact (sq_lt_sq₀ (by positivity) (by positivity)).mpr hTC
    have hm := mul_lt_mul_of_pos_left hsTC hu
    by_contra h
    have hle := mul_le_mul_of_nonneg_right (le_of_not_gt h) (by positivity : 0 ≤ 4*P.β^2)
    nlinarith [hm,hq,hle]
  · rintro ⟨hTeq,hMu⟩
    have hq : T^2*u*coordEffort P^2=4*P.Mm*P.β^2 := by simpa only [hTeq] using hk
    have hTlt : T < 2*P.β/coordEffort P := by
      apply (lt_div_iff₀ hcpos).mpr
      by_contra h
      have hle : (2*P.β)^2 ≤ (T*coordEffort P)^2 := by
        exact pow_le_pow_left₀ (by positivity) (le_of_not_gt h) 2
      have hm := mul_le_mul_of_nonneg_left hle hu.le
      have hMu' := mul_lt_mul_of_pos_right hMu (by positivity : 0 < 4*P.β^2)
      nlinarith [hm,hMu',hq]
    exact ⟨coordinate_of_charge P T u ha hβ hM hR hint hu hT hTlt hq,hTlt⟩
