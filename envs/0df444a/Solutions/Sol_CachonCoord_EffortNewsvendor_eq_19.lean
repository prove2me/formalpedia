-- Prove2me | solution 1 for CachonCoord.EffortNewsvendor.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:33:00.953708+00:00
-- url     : https://prove2.me/submissions/3ce28b3d-82fa-4003-a816-5b67dc4fe6b8

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

end CachonCoord.EffortNewsvendor

open CachonCoord.EffortNewsvendor


theorem solution (M : Model) (wb b q e : ℝ) (hb : 0 < b) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.bbRetailerProfit wb b q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by
  exact eq_19_core M wb b q e hb hq he
