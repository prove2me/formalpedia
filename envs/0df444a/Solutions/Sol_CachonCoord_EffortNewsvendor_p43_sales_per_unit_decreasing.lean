-- Prove2me | solution 1 for CachonCoord.EffortNewsvendor.p43_sales_per_unit_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:34:45.452718+00:00
-- url     : https://prove2.me/submissions/d261532d-a857-47e4-a883-551b2c71cadc

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.EffortNewsvendor

lemma en_cdf_nonpos (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD0 : D (Set.Iio 0) = 0) (h0 : D {0} = 0) (x : ℝ) (hx : x ≤ 0) : cdf D x = 0 := by
  have h1 : D (Set.Iic x) = 0 := by
    apply le_antisymm _ (zero_le)
    calc D (Set.Iic x) ≤ D (Set.Iio 0 ∪ {0}) := measure_mono (by
            intro y hy; simp only [Set.mem_Iic] at hy
            rcases lt_or_eq_of_le (hy.trans hx) with h | h
            · exact Or.inl h
            · exact Or.inr h)
      _ ≤ D (Set.Iio 0) + D {0} := measure_union_le _ _
      _ = 0 := by rw [hD0, h0]; simp
  rw [cdf_eq_real, measureReal_def, h1]; simp

lemma en_ae_nonneg (D : Measure ℝ) (hD0 : D (Set.Iio 0) = 0) : ∀ᵐ d ∂D, 0 ≤ d := by
  rw [ae_iff]; simp only [not_le]; exact hD0

lemma en_leftover (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD0 : D (Set.Iio 0) = 0) (h0 : D {0} = 0) (x : ℝ) :
    ∫ d, max (x - d) 0 ∂D = ∫ y in (0:ℝ)..x, cdf D y := by
  rcases le_or_gt 0 x with hx | hx
  · have hint : Integrable (fun d => max (x - d) 0) D := by
      refine Integrable.mono' (integrable_const x) ?_ ?_
      · exact (by fun_prop : Continuous fun d : ℝ => max (x-d) 0).aestronglyMeasurable
      · filter_upwards [en_ae_nonneg D hD0] with d hd
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) hx
    rw [hint.integral_eq_integral_Ioc_meas_le (M := x)
      (Filter.Eventually.of_forall fun d => le_max_right _ _)]
    · have h2 : ∫ t in Set.Ioc 0 x, D.real {a | t ≤ max (x - a) 0}
          = ∫ t in Set.Ioc 0 x, cdf D (x - t) := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        have : {a : ℝ | t ≤ max (x - a) 0} = Set.Iic (x - t) := by
          ext a; simp only [Set.mem_setOf_eq, Set.mem_Iic]
          constructor
          · intro h; rcases le_max_iff.mp h with h | h
            · linarith
            · linarith [ht.1]
          · intro h; exact le_max_of_le_left (by linarith)
        rw [this, cdf_eq_real]
      rw [h2, ← intervalIntegral.integral_of_le hx, intervalIntegral.integral_comp_sub_left]
      simp
    · filter_upwards [en_ae_nonneg D hD0] with d hd
      exact max_le (by linarith) hx
  · have h1 : ∫ d, max (x - d) 0 ∂D = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ))]
      · simp
      filter_upwards [en_ae_nonneg D hD0] with d hd
      exact max_eq_right (by linarith)
    have h2 : ∫ y in (0:ℝ)..x, cdf D y = ∫ y in (0:ℝ)..x, (0:ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro y hy
      rw [Set.uIcc_of_ge hx.le] at hy
      exact en_cdf_nonpos D hD0 h0 y (by linarith [hy.2])
    rw [h1, h2]; simp

lemma en_int_min (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable (fun x => x) D)
    (q : ℝ) : Integrable (fun d => min q d) D := by
  refine Integrable.mono' ((integrable_const |q|).add hD.norm) ?_ ?_
  · exact (by fun_prop : Continuous fun d : ℝ => min q d).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun d => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rcases le_total q d with h | h
    · rw [min_eq_left h]; linarith [abs_nonneg d]
    · rw [min_eq_right h]; linarith [abs_nonneg q]

lemma en_int_max (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable (fun x => x) D)
    (q : ℝ) : Integrable (fun d => max (q - d) 0) D := by
  have : (fun d => max (q - d) 0) = fun d => q - min q d := by
    funext d; rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
  rw [this]; exact (integrable_const q).sub (en_int_min D hD q)

lemma en_S_eq (M : Model) (q e : ℝ) (he : 0 ≤ e) :
    M.S q e = q - ∫ y in (0 : ℝ)..q, M.F y e := by
  haveI := M.isProb e he
  have hD := M.finite_mean e he
  unfold Model.S Model.F
  rw [← en_leftover (M.law e) (M.nonneg e he) (M.no_atom_zero e he) q]
  have : (fun d => min q d) = fun d => q - max (q - d) 0 := by
    funext d; rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [this, integral_sub (integrable_const q) (en_int_max _ hD q)]
  simp

theorem p41_core (M : Model) (q e : ℝ) (hq : 0 ≤ q) (he : 0 ≤ e) :
    M.S q e = q - ∫ y in (0 : ℝ)..q, M.F y e := en_S_eq M q e he

lemma en_S_deriv (M : Model) (q e : ℝ) (he : 0 < e) :
    HasDerivAt (fun e' => M.S q e') (-∫ y in (0:ℝ)..q, M.effortSlope y e) e := by
  have h := (M.hasDerivAt_integral_cdf e he 0 q).const_sub q
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds he] with t ht
  rw [en_S_eq M q t (le_of_lt ht)]; rfl

lemma en_Pi_deriv (M : Model) (q e : ℝ) (he : 0 < e) :
    HasDerivAt (fun e' => M.Pi q e')
      (M.p * (-∫ y in (0:ℝ)..q, M.effortSlope y e) - M.effortCost' e) e := by
  have := (((en_S_deriv M q e he).const_mul M.p).sub_const (M.c * q)).sub
    (M.hasDerivAt_effortCost e he)
  exact this

lemma en_slope_int_neg (M : Model) (a b e : ℝ) (ha : 0 ≤ a) (hab : a < b) (he : 0 < e) :
    ∫ y in a..b, M.effortSlope y e < 0 := by
  have h := intervalIntegral.intervalIntegral_pos_of_pos_on
    (f := fun y => -M.effortSlope y e) (M.effortSlope_intervalIntegrable e he a b).neg
    (fun y hy => by have := M.effortSlope_neg y e (by linarith [hy.1]) he; linarith) hab
  rw [intervalIntegral.integral_neg] at h
  linarith

lemma en_p_pos (M : Model) : 0 < M.p := by linarith [M.c_nonneg, M.c_lt_p]

theorem eq_18_core (M : Model) (q eo : ℝ) (hq : 0 ≤ q) (heo : 0 < eo)
    (hmax : IsMaxOn (fun e => M.Pi q e) (Set.Ici 0) eo) :
    HasDerivAt (fun e => M.Pi q e)
        (M.p * (-∫ y in (0 : ℝ)..q, M.effortSlope y eo) - M.effortCost' eo) eo ∧
      M.p * (-∫ y in (0 : ℝ)..q, M.effortSlope y eo) - M.effortCost' eo = 0 := by
  have hd := en_Pi_deriv M q eo heo
  refine ⟨hd, ?_⟩
  have hl : IsLocalMax (fun e => M.Pi q e) eo := hmax.isLocalMax (Ici_mem_nhds heo)
  exact hl.hasDerivAt_eq_zero hd

theorem eq_19_core (M : Model) (wb b q e : ℝ) (hb : 0 < b) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.bbRetailerProfit wb b q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by
  have hS := en_S_deriv M q e he
  have h1 := (((hS.const_mul (M.p - b)).sub_const ((wb - b) * q)).sub
    (M.hasDerivAt_effortCost e he))
  refine ⟨_, _, h1, en_Pi_deriv M q e he, ?_⟩
  have := en_slope_int_neg M 0 q e le_rfl hq he
  nlinarith

theorem p42_qf_core (M : Model) (wq δ q e : ℝ) (hwq : 0 < wq) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.qfRetailerProfit wq δ q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by
  have hS := en_S_deriv M q e he
  have hJ := (M.hasDerivAt_integral_cdf e he ((1 - δ) * q) q).const_sub q
  have h1 := (((hS.const_mul M.p).sub (hJ.const_mul wq)).sub
    (M.hasDerivAt_effortCost e he))
  refine ⟨_, _, h1, en_Pi_deriv M q e he, ?_⟩
  have := en_slope_int_neg M ((1 - δ) * q) q e (by nlinarith) (by nlinarith) he
  nlinarith

theorem p42_rs_core (M : Model) (wr φ q e : ℝ) (hφ : φ < 1) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.rsRetailerProfit wr φ q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by
  have hS := en_S_deriv M q e he
  have h1 := (((hS.const_mul (φ * M.p)).sub_const (wr * q)).sub
    (M.hasDerivAt_effortCost e he))
  refine ⟨_, _, h1, en_Pi_deriv M q e he, ?_⟩
  have := en_slope_int_neg M 0 q e le_rfl hq he
  have hp := en_p_pos M
  have : 0 < (1 - φ) * M.p := mul_pos (by linarith) hp
  nlinarith

theorem p42_sr_core (M : Model) (ws r t q e : ℝ) (hr : 0 < r) (ht : 0 ≤ t) (hqt : t < q)
    (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.srRetailerProfit ws r t q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₂ < d₁ := by
  have hS := en_S_deriv M q e he
  have hK := ((M.hasDerivAt_integral_cdf e he t q).const_add t).const_mul r
  have hT : HasDerivAt (fun e' => M.srTransfer ws r t q e')
      (r * ∫ y in t..q, M.effortSlope y e) e := by
    have := hK.const_add ((ws - r) * q)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun e' => ?_)
    simp only [Model.srTransfer, if_neg (not_lt.mpr hqt.le)]; rfl
  have h1 := (((hS.const_mul M.p).sub hT).sub (M.hasDerivAt_effortCost e he))
  refine ⟨_, _, h1, en_Pi_deriv M q e he, ?_⟩
  have := en_slope_int_neg M t q e ht hqt he
  nlinarith

lemma en_qd_eq (M : Model) (lam eo q e : ℝ) (hq : 0 < q) :
    M.qdRetailerProfit lam eo q e =
        M.p * M.S q e - (1 - lam) * M.p * M.S q eo - lam * M.c * q - M.effortCost e
          + (1 - lam) * M.effortCost eo := by
  unfold Model.qdRetailerProfit Model.qdWholesale
  field_simp
  ring

lemma en_qd_sup (M : Model) (lam eo q : ℝ) (hq : 0 < q) :
    M.qdSupplierProfit lam eo q = (1 - lam) * M.Pi q eo := by
  unfold Model.qdSupplierProfit Model.qdWholesale Model.Pi
  field_simp
  ring

theorem p43_qd_core (M : Model) (lam eo q e : ℝ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hq : 0 < q) :
    M.qdRetailerProfit lam eo q e =
        M.p * M.S q e - (1 - lam) * M.p * M.S q eo - lam * M.c * q - M.effortCost e
          + (1 - lam) * M.effortCost eo ∧
      M.qdRetailerProfit lam eo q eo =
        lam * M.p * M.S q eo - lam * M.c * q - lam * M.effortCost eo ∧
      M.qdRetailerProfit lam eo q eo = lam * M.Pi q eo := by
  refine ⟨en_qd_eq M lam eo q e hq, ?_, ?_⟩
  · rw [en_qd_eq M lam eo q eo hq]; ring
  · rw [en_qd_eq M lam eo q eo hq]; unfold Model.Pi; ring


theorem p43_spu_core (M : Model) (e : ℝ) (he : 0 ≤ e) :
    StrictAntiOn (fun q => M.S q e / q) (Set.Ioi 0) := by
  haveI := M.isProb e he
  intro q1 hq1 q2 hq2 h12
  simp only [Set.mem_Ioi] at hq1 hq2
  simp only
  have hmono : Monotone (fun y => M.F y e) := by
    intro a b hab; exact monotone_cdf (M.law e) hab
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun y => M.F y e) volume a b :=
    fun a b => hmono.intervalIntegrable
  rw [en_S_eq M q1 e he, en_S_eq M q2 e he]
  set F1 := M.F q1 e with hF1
  have hA : ∫ y in (0:ℝ)..q1, M.F y e ≤ q1 * F1 := by
    have := intervalIntegral.integral_mono_on hq1.le (hii 0 q1)
      (intervalIntegrable_const (c := F1)) (fun x hx => hmono hx.2)
    simpa using this
  have hB : (q2 - q1) * F1 < ∫ y in q1..q2, M.F y e := by
    have h := intervalIntegral.intervalIntegral_pos_of_pos_on
      (f := fun y => M.F y e - F1) ((hii q1 q2).sub intervalIntegrable_const)
      (fun y hy => by
        have := M.cdf_strictMono e he (Set.mem_Ici.mpr hq1.le)
          (Set.mem_Ici.mpr (by linarith [hy.1])) hy.1
        simp only [Model.F, hF1] at this ⊢; linarith) h12
    rw [intervalIntegral.integral_sub (hii q1 q2) intervalIntegrable_const] at h
    simp at h; linarith
  have hsplit : ∫ y in (0:ℝ)..q2, M.F y e =
      (∫ y in (0:ℝ)..q1, M.F y e) + ∫ y in q1..q2, M.F y e :=
    (intervalIntegral.integral_add_adjacent_intervals (hii 0 q1) (hii q1 q2)).symm
  rw [hsplit]
  set A := ∫ y in (0:ℝ)..q1, M.F y e
  set B := ∫ y in q1..q2, M.F y e
  rw [div_lt_div_iff₀ hq2 hq1]
  nlinarith

theorem goal_core (M : Model) :
    (∀ wb b q e : ℝ, 0 < b → 0 < q → 0 < e →
      ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.bbRetailerProfit wb b q e') d₁ e ∧
        HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂) ∧
    (∀ lam eo : ℝ, 0 ≤ lam → lam ≤ 1 → 0 ≤ eo →
      (∀ q : ℝ, 0 < q → M.qdRetailerProfit lam eo q eo = lam * M.Pi q eo) ∧
      (∀ q : ℝ, 0 < q → M.qdSupplierProfit lam eo q = (1 - lam) * M.Pi q eo) ∧
      (∀ q e : ℝ, 0 < q → 0 < e →
        ∃ d : ℝ, HasDerivAt (fun e' => M.qdRetailerProfit lam eo q e') d e ∧
          HasDerivAt (fun e' => M.Pi q e') d e) ∧
      (∀ q e : ℝ, 0 < q → 0 ≤ e →
        (IsMaxOn (fun e' => M.qdRetailerProfit lam eo q e') (Set.Ici 0) e ↔
          IsMaxOn (fun e' => M.Pi q e') (Set.Ici 0) e))) ∧
    (∀ lam qo eo : ℝ, 0 ≤ lam → lam ≤ 1 → 0 < qo → 0 ≤ eo →
      IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0) (qo, eo) →
      IsMaxOn (fun q => M.qdRetailerProfit lam eo q eo) (Set.Ioi 0) qo ∧
        IsMaxOn (fun q => M.qdSupplierProfit lam eo q) (Set.Ioi 0) qo) := by
  have hret : ∀ lam eo q : ℝ, 0 < q → (fun e' => M.qdRetailerProfit lam eo q e') =
      fun e' => M.Pi q e' + (M.c * q - (1 - lam) * M.p * M.S q eo - lam * M.c * q
        + (1 - lam) * M.effortCost eo) := by
    intro lam eo q hq; funext e'
    rw [en_qd_eq M lam eo q e' hq]; unfold Model.Pi; ring
  have hR : ∀ lam eo q : ℝ, 0 < q → M.qdRetailerProfit lam eo q eo = lam * M.Pi q eo := by
    intro lam eo q hq; rw [en_qd_eq M lam eo q eo hq]; unfold Model.Pi; ring
  refine ⟨fun wb b q e hb hq he => eq_19_core M wb b q e hb hq he, ?_, ?_⟩
  · intro lam eo hl0 hl1 heo
    refine ⟨fun q hq => hR lam eo q hq, fun q hq => en_qd_sup M lam eo q hq, ?_, ?_⟩
    · intro q e hq he
      refine ⟨_, ?_, en_Pi_deriv M q e he⟩
      rw [hret lam eo q hq]
      exact (en_Pi_deriv M q e he).add_const _
    · intro q e hq he
      rw [hret lam eo q hq, isMaxOn_iff, isMaxOn_iff]
      simp only [add_le_add_iff_right]
  · intro lam qo eo hl0 hl1 hqo heo hmax
    rw [isMaxOn_iff] at hmax
    have hP : ∀ q : ℝ, 0 < q → M.Pi q eo ≤ M.Pi qo eo := fun q hq =>
      hmax (q, eo) ⟨Set.mem_Ici.mpr hq.le, Set.mem_Ici.mpr heo⟩
    refine ⟨?_, ?_⟩
    · rw [isMaxOn_iff]; intro q hq
      simp only [Set.mem_Ioi] at hq
      rw [hR lam eo q hq, hR lam eo qo hqo]
      exact mul_le_mul_of_nonneg_left (hP q hq) hl0
    · rw [isMaxOn_iff]; intro q hq
      simp only [Set.mem_Ioi] at hq
      rw [en_qd_sup M lam eo q hq, en_qd_sup M lam eo qo hqo]
      exact mul_le_mul_of_nonneg_left (hP q hq) (by linarith)

end CachonCoord.EffortNewsvendor

open CachonCoord.EffortNewsvendor


theorem solution (M : Model) (e : ℝ) (he : 0 ≤ e) :
    StrictAntiOn (fun q => M.S q e / q) (Set.Ioi 0) := by
  exact p43_spu_core M e he
