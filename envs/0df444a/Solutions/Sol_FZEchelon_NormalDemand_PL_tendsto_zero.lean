-- Prove2me | solution 1 for FZEchelon.NormalDemand.PL_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:26:39.565805+00:00
-- url     : https://prove2.me/submissions/9bda924c-0b88-4026-87bd-e0c787c178ae

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology
open FZEchelon.NormalDemand

instance fzLawProb (D : Data) (i : ℕ) : IsProbabilityMeasure (D.law i) := by
  unfold Data.law; infer_instance

lemma fz_int_id (D : Data) (i : ℕ) : Integrable id (D.law i) := by
  unfold Data.law
  rw [InventoryControl.newsboyDemand_eq]
  exact (memLp_id_gaussianReal 1).integrable (by norm_num)

section generic
variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma fz_ip (hid : Integrable id ν) (x : ℝ) : Integrable (fun t => max (t - x) 0) ν :=
  (hid.sub (integrable_const x)).pos_part

lemma fz_in (hid : Integrable id ν) (x : ℝ) : Integrable (fun t => max (x - t) 0) ν :=
  ((integrable_const x).sub hid).pos_part

lemma fz_lipp (hid : Integrable id ν) (x y : ℝ) :
    |∫ t, max (t - x) 0 ∂ν - ∫ t, max (t - y) 0 ∂ν| ≤ |x - y| := by
  rw [← integral_sub (fz_ip hid x) (fz_ip hid y)]
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun t => max (t - x) 0 - max (t - y) 0) (C := |x - y|)
    (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs]
      calc |max (t - x) 0 - max (t - y) 0| ≤ |(t - x) - (t - y)| := abs_max_sub_max_le_abs _ _ _
        _ = |x - y| := by rw [show (t - x) - (t - y) = -(x - y) by ring, abs_neg])
  simpa using h

lemma fz_lipn (hid : Integrable id ν) (x y : ℝ) :
    |∫ t, max (x - t) 0 ∂ν - ∫ t, max (y - t) 0 ∂ν| ≤ |x - y| := by
  rw [← integral_sub (fz_in hid x) (fz_in hid y)]
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun t => max (x - t) 0 - max (y - t) 0) (C := |x - y|)
    (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs]
      calc |max (x - t) 0 - max (y - t) 0| ≤ |(x - t) - (y - t)| := abs_max_sub_max_le_abs _ _ _
        _ = |x - y| := by rw [show (x - t) - (y - t) = x - y by ring])
  simpa using h

lemma fz_convp (hid : Integrable id ν) (a x y : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ t, max (t - (a * x + (1 - a) * y)) 0 ∂ν
      ≤ a * ∫ t, max (t - x) 0 ∂ν + (1 - a) * ∫ t, max (t - y) 0 ∂ν := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((fz_ip hid x).const_mul a) ((fz_ip hid y).const_mul (1 - a))]
  refine integral_mono (fz_ip hid _) (((fz_ip hid x).const_mul a).add
    ((fz_ip hid y).const_mul (1 - a))) ?_
  intro t
  show max (t - (a * x + (1 - a) * y)) 0 ≤ a * max (t - x) 0 + (1 - a) * max (t - y) 0
  have hb : 0 ≤ 1 - a := by linarith
  apply max_le
  · nlinarith [le_max_left (t - x) 0, le_max_left (t - y) 0]
  · nlinarith [le_max_right (t - x) 0, le_max_right (t - y) 0]

lemma fz_convn (hid : Integrable id ν) (a x y : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ t, max ((a * x + (1 - a) * y) - t) 0 ∂ν
      ≤ a * ∫ t, max (x - t) 0 ∂ν + (1 - a) * ∫ t, max (y - t) 0 ∂ν := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((fz_in hid x).const_mul a) ((fz_in hid y).const_mul (1 - a))]
  refine integral_mono (fz_in hid _) (((fz_in hid x).const_mul a).add
    ((fz_in hid y).const_mul (1 - a))) ?_
  intro t
  show max ((a * x + (1 - a) * y) - t) 0 ≤ a * max (x - t) 0 + (1 - a) * max (y - t) 0
  have hb : 0 ≤ 1 - a := by linarith
  apply max_le
  · nlinarith [le_max_left (x - t) 0, le_max_left (y - t) 0]
  · nlinarith [le_max_right (x - t) 0, le_max_right (y - t) 0]

end generic

section model
variable (D : Data)

/-- Lipschitz constant of `R` (and of `P`, `P^L`). -/
noncomputable def fzK : ℝ := D.hd + D.pr + (D.hd + D.hr)

lemma fz_R_lip (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr) (x y : ℝ) :
    |D.R x - D.R y| ≤ fzK D * |x - y| := by
  have h1 := fz_lipp (fz_int_id D (D.l + 1)) x y
  have h2 := fz_lipn (fz_int_id D (D.l + 1)) x y
  have e : D.R x - D.R y = -D.hd * (x - y)
      + D.pr * ((∫ t, max (t - x) 0 ∂D.law (D.l + 1)) - ∫ t, max (t - y) 0 ∂D.law (D.l + 1))
      + (D.hd + D.hr) * ((∫ t, max (x - t) 0 ∂D.law (D.l + 1))
          - ∫ t, max (y - t) 0 ∂D.law (D.l + 1)) := by
    unfold Data.R; ring
  rw [e]
  refine (abs_add_three _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hhd, abs_of_pos hpr,
    abs_of_pos (by linarith : 0 < D.hd + D.hr)]
  have k1 := mul_le_mul_of_nonneg_left h1 hpr.le
  have k2 := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ D.hd + D.hr)
  unfold fzK
  nlinarith

lemma fz_R_anti (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hx : ∀ x, D.R D.xstar ≤ D.R x) {y z : ℝ} (hyz : y ≤ z) (hz : z ≤ D.xstar) :
    D.R z ≤ D.R y := by
  rcases eq_or_lt_of_le hyz with h | h
  · rw [h]
  have hs : 0 < D.xstar - y := by linarith
  obtain ⟨a, ha, ha1, rfl⟩ : ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ z = a * y + (1 - a) * D.xstar := by
    refine ⟨(D.xstar - z) / (D.xstar - y), div_nonneg (by linarith) hs.le, ?_, ?_⟩
    · rw [div_le_one hs]; linarith
    · field_simp
      ring
  have c1 := fz_convp (fz_int_id D (D.l + 1)) a y D.xstar ha ha1
  have c2 := fz_convn (fz_int_id D (D.l + 1)) a y D.xstar ha ha1
  have e : a * D.R y + (1 - a) * D.R D.xstar - D.R (a * y + (1 - a) * D.xstar)
      = D.pr * (a * (∫ t, max (t - y) 0 ∂D.law (D.l + 1))
          + (1 - a) * (∫ t, max (t - D.xstar) 0 ∂D.law (D.l + 1))
          - ∫ t, max (t - (a * y + (1 - a) * D.xstar)) 0 ∂D.law (D.l + 1))
        + (D.hd + D.hr) * (a * (∫ t, max (y - t) 0 ∂D.law (D.l + 1))
          + (1 - a) * (∫ t, max (D.xstar - t) 0 ∂D.law (D.l + 1))
          - ∫ t, max ((a * y + (1 - a) * D.xstar) - t) 0 ∂D.law (D.l + 1)) := by
    unfold Data.R; ring
  have hnn : 0 ≤ a * D.R y + (1 - a) * D.R D.xstar - D.R (a * y + (1 - a) * D.xstar) := by
    rw [e]
    exact add_nonneg (mul_nonneg hpr.le (by linarith))
      (mul_nonneg (by linarith) (by linarith))
  have h3 := mul_le_mul_of_nonneg_left (hx y) (by linarith : 0 ≤ 1 - a)
  nlinarith

lemma fz_P_nonneg (hx : ∀ x, D.R D.xstar ≤ D.R x) (y : ℝ) : 0 ≤ D.P y := by
  unfold Data.P
  split_ifs
  · exact le_rfl
  · linarith [hx y]

lemma fz_P_zero {y : ℝ} (h : D.xstar ≤ y) : D.P y = 0 := by
  unfold Data.P; rw [if_pos h]

lemma fz_P_lt {y : ℝ} (h : y < D.xstar) : D.P y = D.R y - D.R D.xstar := by
  unfold Data.P; rw [if_neg (not_le.mpr h)]

lemma fzK_nonneg (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr) : 0 ≤ fzK D := by
  unfold fzK; linarith

lemma fz_P_lip (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr) (y z : ℝ) :
    |D.P y - D.P z| ≤ fzK D * |y - z| := by
  have hK := fzK_nonneg D hhd hhr hpr
  rcases le_or_gt D.xstar y with hy | hy <;> rcases le_or_gt D.xstar z with hz | hz
  · rw [fz_P_zero D hy, fz_P_zero D hz, sub_self, abs_zero]
    exact mul_nonneg hK (abs_nonneg _)
  · rw [fz_P_zero D hy, fz_P_lt D hz, zero_sub, abs_neg]
    have h := fz_R_lip D hhd hhr hpr z D.xstar
    have hd : |z - D.xstar| ≤ |y - z| := abs_le.mpr
      ⟨by linarith [le_abs_self (y - z)], by linarith [abs_nonneg (y - z)]⟩
    exact h.trans (mul_le_mul_of_nonneg_left hd hK)
  · rw [fz_P_lt D hy, fz_P_zero D hz, sub_zero]
    have h := fz_R_lip D hhd hhr hpr y D.xstar
    have hd : |y - D.xstar| ≤ |y - z| := abs_le.mpr
      ⟨by linarith [neg_abs_le (y - z)], by linarith [abs_nonneg (y - z)]⟩
    exact h.trans (mul_le_mul_of_nonneg_left hd hK)
  · rw [fz_P_lt D hy, fz_P_lt D hz, show D.R y - D.R D.xstar - (D.R z - D.R D.xstar)
      = D.R y - D.R z by ring]
    exact fz_R_lip D hhd hhr hpr y z

lemma fz_P_anti (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hx : ∀ x, D.R D.xstar ≤ D.R x) {y z : ℝ} (hyz : y ≤ z) : D.P z ≤ D.P y := by
  rcases le_or_gt D.xstar z with hz | hz
  · rw [fz_P_zero D hz]; exact fz_P_nonneg D hx y
  · rw [fz_P_lt D hz, fz_P_lt D (lt_of_le_of_lt hyz hz)]
    linarith [fz_R_anti D hhd hhr hpr hx hyz hz.le]

lemma fz_P_lipW (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr) :
    LipschitzWith (Real.toNNReal (fzK D)) D.P :=
  LipschitzWith.of_dist_le_mul fun y z => by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (fzK_nonneg D hhd hhr hpr)]
    exact fz_P_lip D hhd hhr hpr y z

lemma fz_P_int (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr) (x : ℝ) :
    Integrable (fun t => D.P (x - t)) (D.law D.L) := by
  have hK := fzK_nonneg D hhd hhr hpr
  refine Integrable.mono' ((integrable_const (|D.P 0| + fzK D * |x|)).add
    ((fz_int_id D D.L).abs.const_mul (fzK D)))
    (((fz_P_lipW D hhd hhr hpr).continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (ae_of_all _ fun t => ?_)
  show ‖D.P (x - t)‖ ≤ (|D.P 0| + fzK D * |x|) + fzK D * |id t|
  rw [Real.norm_eq_abs, id]
  have h := fz_P_lip D hhd hhr hpr (x - t) 0
  have h2 : |x - t - 0| ≤ |x| + |t| := by
    rw [sub_zero]
    exact abs_le.mpr ⟨by linarith [neg_abs_le x, le_abs_self t],
      by linarith [le_abs_self x, neg_abs_le t]⟩
  have h3 := abs_sub_abs_le_abs_sub (D.P (x - t)) (D.P 0)
  have h4 := mul_le_mul_of_nonneg_left h2 hK
  nlinarith

lemma fz_PL_lip (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr) (x y : ℝ) :
    |D.PL x - D.PL y| ≤ fzK D * |x - y| := by
  unfold Data.PL
  rw [← integral_sub (fz_P_int D hhd hhr hpr x) (fz_P_int D hhd hhr hpr y)]
  have h := norm_integral_le_of_norm_le_const (μ := D.law D.L)
    (f := fun t => D.P (x - t) - D.P (y - t)) (C := fzK D * |x - y|)
    (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs]
      have := fz_P_lip D hhd hhr hpr (x - t) (y - t)
      rwa [show x - t - (y - t) = x - y by ring] at this)
  simpa using h

lemma fz_PL_anti (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hx : ∀ x, D.R D.xstar ≤ D.R x) : Antitone D.PL := by
  intro x y hxy
  unfold Data.PL
  exact integral_mono (fz_P_int D hhd hhr hpr y) (fz_P_int D hhd hhr hpr x)
    (fun t => fz_P_anti D hhd hhr hpr hx (by linarith : x - t ≤ y - t))

lemma fz_PL_nonneg (hx : ∀ x, D.R D.xstar ≤ D.R x) (x : ℝ) : 0 ≤ D.PL x := by
  unfold Data.PL
  exact integral_nonneg (fun t => fz_P_nonneg D hx (x - t))

end model

theorem solution (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    Tendsto D.PL atTop (𝓝 0) ∧
    ∀ x : ℝ, D.PL x = -∫ t in Set.Ioi x, deriv D.PL t := by
  have htend : Tendsto D.PL atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := D.law D.L) (l := atTop)
      (F := fun x t => D.P (x - t)) (f := fun _ => (0 : ℝ)) (fun t => D.P (0 - t))
      (Eventually.of_forall fun x => (fz_P_int D hhd hhr hpr x).aestronglyMeasurable)
      ((eventually_ge_atTop 0).mono fun x hx0 => ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (fz_P_nonneg D hx _)]
        exact fz_P_anti D hhd hhr hpr hx (by linarith : 0 - t ≤ x - t))
      (fz_P_int D hhd hhr hpr 0)
      (ae_of_all _ fun t => tendsto_const_nhds.congr'
        ((eventually_ge_atTop (D.xstar + t)).mono fun x hx' =>
          (fz_P_zero D (by linarith : D.xstar ≤ x - t)).symm))
    show Tendsto (fun x => ∫ t, D.P (x - t) ∂(D.law D.L)) atTop (𝓝 0)
    simpa using h
  refine ⟨htend, fun x => ?_⟩
  have hK := fzK_nonneg D hhd hhr hpr
  have hLip : LipschitzWith (Real.toNNReal (fzK D)) D.PL :=
    LipschitzWith.of_dist_le_mul fun y z => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
      exact fz_PL_lip D hhd hhr hpr y z
  have hAC : ∀ b, AbsolutelyContinuousOnInterval D.PL x b := fun b =>
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hd0 : ∀ t, deriv D.PL t ≤ 0 := fun t => (fz_PL_anti D hhd hhr hpr hx).deriv_nonpos
  have hint : IntegrableOn (deriv D.PL) (Set.Ioi x) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (D.PL x) x
      (fun i => (hAC i).intervalIntegrable_deriv.1) tendsto_id ?_
    filter_upwards [eventually_ge_atTop x] with i hi
    have e : ∫ t in x..i, ‖deriv D.PL t‖ = ∫ t in x..i, -deriv D.PL t :=
      intervalIntegral.integral_congr (fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonpos (hd0 t)])
    rw [e, intervalIntegral.integral_neg, (hAC i).integral_deriv_eq_sub]
    linarith [fz_PL_nonneg D hx i]
  have hlim1 := intervalIntegral_tendsto_integral_Ioi x hint tendsto_id
  have hlim2 : Tendsto (fun b => ∫ t in x..id b, deriv D.PL t) atTop (𝓝 (0 - D.PL x)) :=
    Tendsto.congr (fun b => ((hAC b).integral_deriv_eq_sub).symm) (htend.sub_const (D.PL x))
  have := tendsto_nhds_unique hlim1 hlim2
  linarith
