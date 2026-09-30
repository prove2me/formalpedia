-- Prove2me | solution 1 for ChatterjeeSamuelson.UniformEquilibrium.linear_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:04:53.04851+00:00
-- url     : https://prove2.me/submissions/6b738584-921f-4716-afd8-a1a80395f217

import Definitions.Def_ChatterjeeSamuelson_Shared_unif
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Set
open ChatterjeeSamuelson

private noncomputable def pay (k : ℝ) (S : ℝ → ℝ) (b v y : ℝ) : ℝ :=
  if S y ≤ b then v-(k*b+(1-k)*S y) else 0
private noncomputable def raw (k V : ℝ) (S : ℝ → ℝ) (b v : ℝ) : ℝ :=
  ∫ y in Icc 0 V, pay k S b v y

private theorem profit_raw (k V : ℝ) (S : ℝ → ℝ) (b v : ℝ) (hV : 0 ≤ V) :
    Shared.buyerProfit k (Shared.unif V) S b v = V⁻¹ * raw k V S b v := by
  unfold Shared.buyerProfit Shared.unif ProbabilityTheory.cond raw pay
  rw [integral_smul_measure]
  simp [Real.volume_Icc,ENNReal.toReal_inv,ENNReal.toReal_ofReal hV]

private theorem pay_integrable (k V : ℝ) (S : ℝ → ℝ) (b v : ℝ)
    (hS : Measurable S) (hpos : ∀ y ∈ Icc 0 V, 0 ≤ S y) :
    IntegrableOn (pay k S b v) (Icc 0 V) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    (show Measurable (pay k S b v) from Measurable.ite (measurableSet_le hS measurable_const)
      (measurable_const.sub (measurable_const.add (measurable_const.mul hS))) measurable_const).aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro y hy
  unfold pay
  split_ifs with hb
  · have hs := hpos y hy
    have hsb : |S y| ≤ |b| := by rw [abs_of_nonneg hs]; exact hb.trans (le_abs_self _)
    calc
      ‖v-(k*b+(1-k)*S y)‖ ≤ |v| + (|k*b| + |1-k| * |S y|) := by
        simp only [Real.norm_eq_abs]
        have h1:=abs_sub v (k*b+(1-k)*S y)
        have h2:=abs_add_le (k*b) ((1-k)*S y)
        rw [abs_mul (1-k) (S y)] at h2
        linarith
      _ ≤ |v| + (|k*b| + |1-k| * |b|) := by gcongr
  · simp only [norm_zero]
    positivity

private theorem affine_integral (c A B : ℝ) (hc : 0 ≤ c) :
    (∫ y in Icc (0:ℝ) c, A-B*y) = A*c-B*c^2/2 := by
  have hA : IntervalIntegrable (fun _ : ℝ => A) volume 0 c := continuous_const.intervalIntegrable _ _
  have hB : IntervalIntegrable (fun x : ℝ => B*x) volume 0 c := (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hc,
    intervalIntegral.integral_sub hA hB,intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,integral_id]
  simp only [sub_zero,zero_pow (by decide : 2≠0),smul_eq_mul]
  ring

private theorem raw_middle (k V : ℝ) (S : ℝ → ℝ) (b v : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hV : 0 < V)
    (hS_eq : ∀ y, 0 ≤ y → y ≤ (2-k)/2*V → S y=Shared.sellerLinear k V y)
    (hS_ge : ∀ y, (2-k)/2*V < y → y ≤ V → Shared.sellerLinear k V y ≤ S y)
    (hb0 : (1-k)/2*V ≤ b) (hb1 : b ≤ (2-k)/2*V) :
    raw k V S b v = (2-k)*((v-(1-k)/2*V)*(b-(1-k)/2*V)
      -(1+k)/2*(b-(1-k)/2*V)^2) := by
  let a := (1-k)/2*V
  let t := (2-k)/2*V
  let d := 2-k
  let c := d*(b-a)
  have hd : 0 < d := by dsimp [d]; linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htV : t ≤ V := by dsimp [t]; nlinarith
  have hc0 : 0 ≤ c := mul_nonneg hd.le (sub_nonneg.mpr hb0)
  have hct : c ≤ t := by dsimp [c,d,a,t] at *; nlinarith
  have hcV : c ≤ V := hct.trans htV
  have hb : b=a+c/d := by dsimp [c]; field_simp; ring
  have hiff : ∀ y ∈ Icc 0 V, S y ≤ b ↔ y ≤ c := by
    intro y hy
    by_cases hyt : y ≤ t
    · rw [hS_eq y hy.1 hyt]
      simp only [Shared.sellerLinear]
      change y/d+a ≤ b ↔ y ≤ c
      rw [←le_sub_iff_add_le,div_le_iff₀ hd]
      dsimp [c]
      ring_nf
    · have hsg:=hS_ge y (lt_of_not_ge hyt) hy.2
      have hbS : b < S y := by
        have htc : t = a+t/d := by dsimp [t,a,d]; field_simp [show 2-k ≠ 0 by linarith]; ring
        have hlt : t < Shared.sellerLinear k V y := by
          change t < y/d+a
          rw [htc]
          linarith [div_lt_div_of_pos_right (lt_of_not_ge hyt) hd]
        exact lt_of_le_of_lt hb1 (hlt.trans_le hsg)
      exact iff_of_false (not_le.mpr hbS) (not_le.mpr (hct.trans_lt (lt_of_not_ge hyt)))
  have heq : raw k V S b v = ∫ y in Icc 0 c, (v-k*b-(1-k)*a)-((1-k)/d)*y := by
    unfold raw
    calc
      _ = ∫ y in Icc 0 V, (Icc 0 c).indicator (fun y => (v-k*b-(1-k)*a)-((1-k)/d)*y) y := by
        apply integral_congr_ae
        apply ae_restrict_of_forall_mem measurableSet_Icc
        intro y hy
        unfold pay
        simp only [hiff y hy]
        by_cases hyc : y ≤ c
        · rw [if_pos hyc,indicator_of_mem (show y ∈ Icc 0 c from ⟨hy.1,hyc⟩),hS_eq y hy.1 (hyc.trans hct)]
          simp only [Shared.sellerLinear]
          dsimp [a,d]
          ring
        · rw [if_neg hyc,indicator_of_notMem (by simp [hyc])]
      _ = _ := by
        rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
        rw [inter_eq_left.mpr (Icc_subset_Icc le_rfl hcV)]
  rw [heq,affine_integral c _ _ hc0]
  dsimp [c,d,a]
  field_simp [show 2-k ≠ 0 by linarith]
  ring

private theorem seller_lower (k V : ℝ) (S : ℝ → ℝ) (hk1 : k ≤ 1) (hV : 0 < V)
    (hS_eq : ∀ y, 0 ≤ y → y ≤ (2-k)/2*V → S y=Shared.sellerLinear k V y)
    (hS_ge : ∀ y, (2-k)/2*V < y → y ≤ V → Shared.sellerLinear k V y ≤ S y) :
    ∀ y ∈ Icc 0 V, Shared.sellerLinear k V y ≤ S y := by
  intro y hy
  by_cases ht : y ≤ (2-k)/2*V
  · exact (hS_eq y hy.1 ht).ge
  · exact hS_ge y (lt_of_not_ge ht) hy.2

private theorem raw_below (k V : ℝ) (S : ℝ → ℝ) (b v : ℝ)
    (hk1 : k ≤ 1) (hV : 0 < V)
    (hS : ∀ y ∈ Icc 0 V, Shared.sellerLinear k V y ≤ S y)
    (hb : b < (1-k)/2*V) : raw k V S b v=0 := by
  unfold raw
  apply integral_eq_zero_of_ae
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro y hy
  have hh:=hS y hy
  have hy0 : 0 ≤ y/(2-k) := div_nonneg hy.1 (by linarith)
  have hbS : b < S y := by simp only [Shared.sellerLinear] at hh; linarith
  simp [pay,not_le.mpr hbS]

private theorem raw_above (k V : ℝ) (S : ℝ → ℝ) (b v : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hV : 0 < V) (hv : v ≤ V) (hSm : Measurable S)
    (hS_eq : ∀ y, 0 ≤ y → y ≤ (2-k)/2*V → S y=Shared.sellerLinear k V y)
    (hS_ge : ∀ y, (2-k)/2*V < y → y ≤ V → Shared.sellerLinear k V y ≤ S y)
    (hb : (2-k)/2*V ≤ b) : raw k V S b v ≤ raw k V S ((2-k)/2*V) v := by
  let a := (1-k)/2*V
  let t := (2-k)/2*V
  let d := 2-k
  let c := d*(b-a)
  let μ := volume.restrict (Icc (0:ℝ) V)
  have hd : 0 < d := by dsimp [d]; linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htV : t ≤ V := by dsimp [t]; nlinarith
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hta : t = a+t/d := by dsimp [t,a,d]; field_simp [show 2-k ≠ 0 by linarith]; ring
  have htc : t ≤ c := by
    have hb' : a+t/d ≤ b := by rwa [←hta]
    have := (div_le_iff₀ hd).mp (show t/d ≤ b-a by linarith)
    dsimp [c]; nlinarith
  have hlow:=seller_lower k V S hk1 hV hS_eq hS_ge
  have hpos : ∀ y ∈ Icc 0 V, 0 ≤ S y := by
    intro y hy
    have hh:=hlow y hy
    have hp : 0 ≤ y/(2-k) := div_nonneg hy.1 (by linarith)
    simp only [Shared.sellerLinear] at hh
    change y/(2-k)+a ≤ S y at hh
    linarith
  have hi_b:=pay_integrable k V S b v hSm hpos
  have hi_t:=pay_integrable k V S t v hSm hpos
  have hi0 : Integrable ((Icc 0 t).indicator (fun _ : ℝ => k*(b-t))) μ :=
    (integrable_const _).indicator measurableSet_Icc
  have hi1 : Integrable ((Ioc t c).indicator (fun _ : ℝ => V-t)) μ :=
    (integrable_const _).indicator measurableSet_Ioc
  have hbound : raw k V S b v ≤ raw k V S t v
      - t*(k*(b-t)) + μ.real (Ioc t c)*(V-t) := by
    have hh : (∫ y, pay k S b v y ∂μ) ≤ ∫ y,
        pay k S t v y - (Icc 0 t).indicator (fun _ : ℝ => k*(b-t)) y
          + (Ioc t c).indicator (fun _ : ℝ => V-t) y ∂μ := by
      apply integral_mono_ae hi_b ((hi_t.sub hi0).add hi1)
      apply ae_restrict_of_forall_mem measurableSet_Icc
      intro y hy
      dsimp only [Pi.add_apply,Pi.sub_apply]
      by_cases hyt : y ≤ t
      · have hsy := hS_eq y hy.1 hyt
        have hSt : S y ≤ t := by
          rw [hsy]; change y/d+a ≤ t
          calc y/d+a ≤ t/d+a := by gcongr
               _ = t := by linarith [hta]
        simp only [pay,if_pos hSt,if_pos (hSt.trans hb),
          indicator_of_mem (show y ∈ Icc 0 t from ⟨hy.1,hyt⟩),
          indicator_of_notMem (show y ∉ Ioc t c from fun h => (not_lt_of_ge hyt) h.1),add_zero]
        ring_nf
        exact le_rfl
      · have hyt' : t < y := lt_of_not_ge hyt
        have hSt : t < S y := by
          have hh:=hlow y hy
          have : t < Shared.sellerLinear k V y := by
            change t < y/d+a
            rw [hta]
            linarith [div_lt_div_of_pos_right hyt' hd]
          exact this.trans_le hh
        simp only [pay,if_neg (not_le.mpr hSt),zero_sub,
          indicator_of_notMem (show y ∉ Icc 0 t by simp [hyt]),neg_zero,zero_add]
        split_ifs with hSb
        · have hyc : y ≤ c := by
            have hh := (hlow y hy).trans hSb
            change y/d+a ≤ b at hh
            have := (div_le_iff₀ hd).mp (show y/d ≤ b-a by linarith)
            dsimp [c]; nlinarith
          rw [indicator_of_mem (show y ∈ Ioc t c from ⟨hyt',hyc⟩)]
          have h1:=mul_le_mul_of_nonneg_left hb hk0
          have h2:=mul_le_mul_of_nonneg_left hSt.le (show 0 ≤ 1-k by linarith)
          nlinarith
        · exact indicator_nonneg (fun _ _ => sub_nonneg.mpr htV) _
    have headd := integral_add (μ:=μ)
      (f:=fun y => pay k S t v y - (Icc 0 t).indicator (fun _ : ℝ => k*(b-t)) y)
      (g:=(Ioc t c).indicator (fun _ : ℝ => V-t)) (hi_t.sub hi0) hi1
    have hesub := integral_sub (μ:=μ) (f:=pay k S t v)
      (g:=(Icc 0 t).indicator (fun _ : ℝ => k*(b-t))) hi_t hi0
    rw [headd,hesub,integral_indicator_const _ measurableSet_Icc,
      integral_indicator_const _ measurableSet_Ioc] at hh
    have hm : μ.real (Icc 0 t)=t := by
      dsimp [μ]
      rw [measureReal_restrict_apply measurableSet_Icc,inter_eq_left.mpr (Icc_subset_Icc le_rfl htV)]
      simpa using (Real.volume_real_Icc_of_le ht0)
    simpa only [hm,smul_eq_mul,raw,μ] using hh
  have hm : μ.real (Ioc t c) ≤ c-t := by
    dsimp [μ]
    rw [measureReal_restrict_apply measurableSet_Ioc]
    exact (measureReal_mono inter_subset_left (by simp [Real.volume_Ioc])).trans_eq (Real.volume_real_Ioc_of_le htc)
  have hfinal:=mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr htV)
  have he : (c-t)*(V-t)=t*(k*(b-t)) := by
    dsimp [c,d,t,a]
    ring
  rw [he] at hfinal
  linarith

private theorem buyer_raw_best (k V : ℝ) (S B : ℝ → ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hV : 0 < V) (hSm : Measurable S)
    (hS_eq : ∀ y, 0 ≤ y → y ≤ (2-k)/2*V → S y=Shared.sellerLinear k V y)
    (hS_ge : ∀ y, (2-k)/2*V < y → y ≤ V → Shared.sellerLinear k V y ≤ S y)
    (hB_le : ∀ v, 0 ≤ v → v < (1-k)/2*V → B v ≤ Shared.buyerLinear k V v)
    (hB_eq : ∀ v, (1-k)/2*V ≤ v → v ≤ V → B v=Shared.buyerLinear k V v) :
    ∀ v ∈ Icc 0 V, ∀ b, raw k V S b v ≤ raw k V S (B v) v := by
  let a := (1-k)/2*V
  let t := (2-k)/2*V
  let d := 2-k
  have hd : 0 < d := by dsimp [d]; linarith
  have he : 0 < 1+k := by linarith
  have hat : a ≤ t := by dsimp [a,t]; nlinarith
  have hlow:=seller_lower k V S hk1 hV hS_eq hS_ge
  intro v hv
  have hmid:=raw_middle k V S
  have hmid' : ∀ b, a ≤ b → b ≤ t → raw k V S b v =
      d*((v-a)*(b-a)-(1+k)/2*(b-a)^2) := by
    intro b hb0 hb1
    exact raw_middle k V S b v hk0 hk1 hV hS_eq hS_ge hb0 hb1
  have hcap : ∀ b, t ≤ b → raw k V S b v ≤ raw k V S t v := by
    intro b hb
    exact raw_above k V S b v hk0 hk1 hV hv.2 hSm hS_eq hS_ge hb
  by_cases hva : v < a
  · have hB : B v < a := by
      have hh:=hB_le v hv.1 hva
      have heq : Shared.buyerLinear k V v = a+(v-a)/(1+k) := by
        dsimp [Shared.buyerLinear,a]
        field_simp
        ring
      rw [heq] at hh
      have hneg:=div_neg_of_neg_of_pos (sub_neg.mpr hva) he
      linarith
    rw [raw_below k V S (B v) v hk1 hV hlow hB]
    have hmiddle : ∀ b, a ≤ b → b ≤ t → raw k V S b v ≤ 0 := by
      intro b hb0 hb1
      rw [hmid' b hb0 hb1]
      apply mul_nonpos_of_nonneg_of_nonpos hd.le
      have h1:=mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hva.le) (sub_nonneg.mpr hb0)
      have h2:=mul_nonneg (show 0 ≤ (1+k)/2 by positivity) (sq_nonneg (b-a))
      linarith
    intro b
    by_cases hb0 : b < a
    · rw [raw_below k V S b v hk1 hV hlow hb0]
    · by_cases hb1 : b ≤ t
      · exact hmiddle b (le_of_not_gt hb0) hb1
      · exact (hcap b (le_of_not_ge hb1)).trans (hmiddle t hat le_rfl)
  · have hva' : a ≤ v := le_of_not_gt hva
    have hB:=hB_eq v hva' hv.2
    have hrel : v-a=(1+k)*(B v-a) := by
      rw [hB]
      dsimp [Shared.buyerLinear,a]
      field_simp
      ring
    have hBa : a ≤ B v := by nlinarith
    have hBt : B v ≤ t := by
      have htt : V-a=(1+k)*(t-a) := by dsimp [a,t]; ring
      nlinarith [hv.2]
    have hopt : ∀ b, d*((v-a)*(b-a)-(1+k)/2*(b-a)^2) ≤
        d*((v-a)*(B v-a)-(1+k)/2*(B v-a)^2) := by
      intro b
      have hsq:=mul_nonneg (mul_nonneg hd.le (show 0 ≤ (1+k)/2 by positivity)) (sq_nonneg (b-B v))
      rw [hrel]
      nlinarith
    have hnonneg : 0 ≤ raw k V S (B v) v := by
      rw [hmid' (B v) hBa hBt]
      simpa using hopt a
    intro b
    by_cases hb0 : b < a
    · rw [raw_below k V S b v hk1 hV hlow hb0]
      exact hnonneg
    · have hmiddle : ∀ c, a ≤ c → c ≤ t → raw k V S c v ≤ raw k V S (B v) v := by
        intro c hc0 hc1
        rw [hmid' c hc0 hc1,hmid' (B v) hBa hBt]
        exact hopt c
      by_cases hb1 : b ≤ t
      · exact hmiddle b (le_of_not_gt hb0) hb1
      · exact (hcap b (le_of_not_ge hb1)).trans (hmiddle t hat le_rfl)

private theorem buyer_best (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hvbar : 0 < vbar)
    (S B : ℝ → ℝ) (hSmeas : Measurable S) (hBmeas : Measurable B)
    (hS_eq : ∀ v, 0 ≤ v → v ≤ (2 - k) / 2 * vbar → S v = Shared.sellerLinear k vbar v)
    (hS_ge : ∀ v, (2 - k) / 2 * vbar < v → v ≤ vbar → Shared.sellerLinear k vbar v ≤ S v)
    (hB_le : ∀ v, 0 ≤ v → v < (1 - k) / 2 * vbar → B v ≤ Shared.buyerLinear k vbar v)
    (hB_eq : ∀ v, (1 - k) / 2 * vbar ≤ v → v ≤ vbar → B v = Shared.buyerLinear k vbar v) :
    ∀ v ∈ Icc (0 : ℝ) vbar, ∀ b : ℝ,
      Shared.buyerProfit k (Shared.unif vbar) S b v ≤ Shared.buyerProfit k (Shared.unif vbar) S (B v) v := by
  intro v hv b
  rw [profit_raw k vbar S b v hvbar.le,profit_raw k vbar S (B v) v hvbar.le]
  exact mul_le_mul_of_nonneg_left
    (buyer_raw_best k vbar S B hk0 hk1 hvbar hSmeas hS_eq hS_ge hB_le hB_eq v hv b)
    (inv_nonneg.mpr hvbar.le)


private theorem unif_reflect (V : ℝ) (hV : 0 ≤ V) (F : ℝ → ℝ) :
    (∫ x, F (V-x) ∂(Shared.unif V)) = ∫ x, F x ∂(Shared.unif V) := by
  unfold Shared.unif ProbabilityTheory.cond
  rw [integral_smul_measure,integral_smul_measure]
  congr 1
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hV,←intervalIntegral.integral_of_le hV,
    intervalIntegral.integral_comp_sub_left]
  simp

private theorem profit_reflect (k V : ℝ) (B : ℝ → ℝ) (s v : ℝ) (hV : 0 ≤ V) :
    Shared.sellerProfit k (Shared.unif V) B s v =
      Shared.buyerProfit (1-k) (Shared.unif V) (fun y => V-B (V-y)) (V-s) (V-v) := by
  unfold Shared.sellerProfit Shared.buyerProfit
  rw [←unif_reflect V hV (fun y => if s ≤ B y then k*B y+(1-k)*s-v else 0)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  have hi : s ≤ B (V-y) ↔ V-B (V-y) ≤ V-s := by constructor <;> intro h <;> linarith
  simp only [←hi]
  split_ifs <;> ring

private theorem reflected_rules (k V : ℝ) (S B : ℝ → ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hV : 0 < V)
    (hS_eq : ∀ y, 0 ≤ y → y ≤ (2-k)/2*V → S y=Shared.sellerLinear k V y)
    (hS_ge : ∀ y, (2-k)/2*V < y → y ≤ V → Shared.sellerLinear k V y ≤ S y)
    (hB_le : ∀ v, 0 ≤ v → v < (1-k)/2*V → B v ≤ Shared.buyerLinear k V v)
    (hB_eq : ∀ v, (1-k)/2*V ≤ v → v ≤ V → B v=Shared.buyerLinear k V v) :
    (∀ y, 0 ≤ y → y ≤ (2-(1-k))/2*V → V-B (V-y)=Shared.sellerLinear (1-k) V y) ∧
    (∀ y, (2-(1-k))/2*V < y → y ≤ V → Shared.sellerLinear (1-k) V y ≤ V-B (V-y)) ∧
    (∀ v, 0 ≤ v → v < (1-(1-k))/2*V → V-S (V-v) ≤ Shared.buyerLinear (1-k) V v) ∧
    (∀ v, (1-(1-k))/2*V ≤ v → v ≤ V → V-S (V-v)=Shared.buyerLinear (1-k) V v) := by
  have hd : 2-k ≠ 0 := by linarith
  have he : 1+k ≠ 0 := by linarith
  have e1 : ∀ y, V-Shared.buyerLinear k V (V-y)=Shared.sellerLinear (1-k) V y := by
    intro y
    simp only [Shared.buyerLinear,Shared.sellerLinear]
    have : 2-(1-k)=1+k := by ring
    rw [this]
    field_simp
    ring
  have e2 : ∀ y, V-Shared.sellerLinear k V (V-y)=Shared.buyerLinear (1-k) V y := by
    intro y
    simp only [Shared.buyerLinear,Shared.sellerLinear]
    have : 1+(1-k)=2-k := by ring
    rw [this]
    field_simp
    ring
  refine ⟨?_,?_,?_,?_⟩
  · intro y hy0 hy1
    rw [hB_eq (V-y) (by nlinarith) (by linarith),e1]
  · intro y hy0 hy1
    rw [←e1]
    have hh:=hB_le (V-y) (by linarith) (by nlinarith)
    linarith
  · intro v hv0 hv1
    rw [←e2]
    have hh:=hS_ge (V-v) (by nlinarith) (by linarith)
    linarith
  · intro v hv0 hv1
    rw [hS_eq (V-v) (by linarith) (by nlinarith),e2]

private theorem seller_best (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hvbar : 0 < vbar)
    (S B : ℝ → ℝ) (hSmeas : Measurable S) (hBmeas : Measurable B)
    (hS_eq : ∀ v, 0 ≤ v → v ≤ (2 - k) / 2 * vbar → S v = Shared.sellerLinear k vbar v)
    (hS_ge : ∀ v, (2 - k) / 2 * vbar < v → v ≤ vbar → Shared.sellerLinear k vbar v ≤ S v)
    (hB_le : ∀ v, 0 ≤ v → v < (1 - k) / 2 * vbar → B v ≤ Shared.buyerLinear k vbar v)
    (hB_eq : ∀ v, (1 - k) / 2 * vbar ≤ v → v ≤ vbar → B v = Shared.buyerLinear k vbar v) :
    ∀ v ∈ Icc (0 : ℝ) vbar, ∀ s : ℝ,
      Shared.sellerProfit k (Shared.unif vbar) B s v ≤ Shared.sellerProfit k (Shared.unif vbar) B (S v) v := by
  obtain ⟨h1,h2,h3,h4⟩:=reflected_rules k vbar S B hk0 hk1 hvbar hS_eq hS_ge hB_le hB_eq
  have hSm : Measurable (fun y => vbar-B (vbar-y)) :=
    measurable_const.sub (hBmeas.comp (measurable_const.sub measurable_id))
  have hBm : Measurable (fun y => vbar-S (vbar-y)) :=
    measurable_const.sub (hSmeas.comp (measurable_const.sub measurable_id))
  intro v hv s
  rw [profit_reflect k vbar B s v hvbar.le,profit_reflect k vbar B (S v) v hvbar.le]
  have hh:=buyer_best (1-k) vbar (by linarith) (by linarith) hvbar
    (fun y => vbar-B (vbar-y)) (fun y => vbar-S (vbar-y)) hSm hBm h1 h2 h3 h4
    (vbar-v) ⟨by linarith [hv.2],by linarith [hv.1]⟩ (vbar-s)
  simpa only [sub_sub_cancel] using hh

theorem solution (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hvbar : 0 < vbar)
    (S B : ℝ → ℝ) (hSmeas : Measurable S) (hBmeas : Measurable B)
    (hS_eq : ∀ v, 0 ≤ v → v ≤ (2 - k) / 2 * vbar → S v = Shared.sellerLinear k vbar v)
    (hS_ge : ∀ v, (2 - k) / 2 * vbar < v → v ≤ vbar → Shared.sellerLinear k vbar v ≤ S v)
    (hB_le : ∀ v, 0 ≤ v → v < (1 - k) / 2 * vbar → B v ≤ Shared.buyerLinear k vbar v)
    (hB_eq : ∀ v, (1 - k) / 2 * vbar ≤ v → v ≤ vbar → B v = Shared.buyerLinear k vbar v) :
    Shared.IsEquilibrium k (Shared.unif vbar) (Shared.unif vbar) 0 vbar 0 vbar S B := by
  exact ⟨buyer_best k vbar hk0 hk1 hvbar S B hSmeas hBmeas hS_eq hS_ge hB_le hB_eq,
    seller_best k vbar hk0 hk1 hvbar S B hSmeas hBmeas hS_eq hS_ge hB_le hB_eq⟩
