-- Prove2me | solution 1 for DepthOneQExp.hh09_lemma1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:09:19.161386+00:00
-- url     : https://prove2.me/submissions/3c873178-c9fa-46ee-835a-a8d6642c5940

import Mathlib
set_option linter.deprecated false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace

namespace DepthOneQExp.HH09Aux

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

section
variable (P : E →L[ℂ] E) (hPP : P * P = P) (hPadj : ContinuousLinearMap.adjoint P = P)
include hPP hPadj

theorem P_adj (a b : E) : ⟪P a, b⟫_ℂ = ⟪a, P b⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, hPadj]

theorem P_idem (a : E) : P (P a) = P a := by
  rw [← ContinuousLinearMap.mul_apply, hPP]

theorem P_orth (a b : E) : ⟪P a, b - P b⟫_ℂ = 0 := by
  rw [inner_sub_right, P_adj P hPP hPadj a b, P_adj P hPP hPadj a (P b), P_idem P hPP hPadj, sub_self]

theorem pyth (a : E) : ‖a‖ ^ 2 = ‖P a‖ ^ 2 + ‖a - P a‖ ^ 2 := by
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P a) (a - P a) (P_orth P hPP hPadj a a)
  rw [add_sub_cancel] at this
  nlinarith [this]
end

/-- The X-step: for unit `u`, `v`, `Re⟨u, Xv⟩ ≤ 1 - εX (1 - ‖d‖²)` with `d = (Pu + Pv)/2`. -/
theorem xstep (P X : E →L[ℂ] E) (hPP : P * P = P) (hPadj : ContinuousLinearMap.adjoint P = P)
    (hPX : P * X = P) (hXP : X * P = P) (εX : ℝ) (hεX : εX ≤ 1)
    (hX' : ‖(1 - P) * X * (1 - P)‖ ≤ 1 - εX) (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    RCLike.re ⟪u, X v⟫_ℂ ≤ 1 - εX * (1 - ‖(1 / 2 : ℂ) • (P u + P v)‖ ^ 2) := by
  set yu := u - P u
  set yv := v - P v
  have hXv : X v = P v + ((1 - P) * X * (1 - P)) yv := by
    have h1 : X (P v) = P v := by rw [← ContinuousLinearMap.mul_apply, hXP]
    have h2 : P (X yv) = 0 := by
      rw [← ContinuousLinearMap.mul_apply, hPX]
      simp [yv, P_idem P hPP hPadj]
    have h3 : (1 - P) yv = yv := by simp [yv, P_idem P hPP hPadj]
    simp only [ContinuousLinearMap.mul_apply, h3, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, h2, sub_zero]
    rw [← h1, ← map_add]
    congr 1
    simp [yv]
  have hin1 : ⟪u, P v⟫_ℂ = ⟪P u, P v⟫_ℂ := by
    rw [P_adj P hPP hPadj, P_idem P hPP hPadj]
  have hin2 : ⟪u, ((1 - P) * X * (1 - P)) yv⟫_ℂ = ⟪yu, ((1 - P) * X * (1 - P)) yv⟫_ℂ := by
    have : ⟪P u, ((1 - P) * X * (1 - P)) yv⟫_ℂ = 0 := by
      rw [P_adj P hPP hPadj]
      have : P (((1 - P) * X * (1 - P)) yv) = 0 := by
        simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.one_apply, map_sub, P_idem P hPP hPadj, sub_self]
      rw [this, inner_zero_right]
    rw [show yu = u - P u from rfl, inner_sub_left, this, sub_zero]
  rw [hXv, inner_add_right, hin1, hin2, map_add]
  have hX2 : RCLike.re ⟪yu, ((1 - P) * X * (1 - P)) yv⟫_ℂ ≤ (1 - εX) * (‖yu‖ * ‖yv‖) := by
    refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    calc ‖yu‖ * ‖((1 - P) * X * (1 - P)) yv‖ ≤ ‖yu‖ * (‖(1 - P) * X * (1 - P)‖ * ‖yv‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖yu‖ * ((1 - εX) * ‖yv‖) := by gcongr
      _ = (1 - εX) * (‖yu‖ * ‖yv‖) := by ring
  have hpu := pyth P hPP hPadj u
  have hpv := pyth P hPP hPadj v
  have hR : RCLike.re ⟪P u, P v⟫_ℂ ≤ ‖P u‖ * ‖P v‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hd : ‖(1 / 2 : ℂ) • (P u + P v)‖ ^ 2 =
      (‖P u‖ ^ 2 + ‖P v‖ ^ 2 + 2 * RCLike.re ⟪P u, P v⟫_ℂ) / 4 := by
    rw [norm_smul, mul_pow, @norm_add_sq ℂ]
    norm_num
    ring
  rw [hd]
  rw [hu] at hpu; rw [hv] at hpv
  set ru := ‖P u‖; set rv := ‖P v‖; set cu := ‖yu‖; set cv := ‖yv‖
  set R := RCLike.re ⟪P u, P v⟫_ℂ
  have hcu : 0 ≤ cu := norm_nonneg _
  have hcv : 0 ≤ cv := norm_nonneg _
  nlinarith [sq_nonneg (cu - cv), sq_nonneg (ru - rv), mul_nonneg (sub_nonneg.2 hεX) (sq_nonneg (cu - cv))]

/-- final scalar inequality of the Y-step -/
theorem ystep_alg (A B E y α1 α2 β1 β2 εY : ℝ) (hεY0 : 0 < εY) (hεY1 : εY ≤ 1)
    (hAB : A + B = 1) (hB : B ≤ εY / 12) (hB0 : 0 ≤ B) (hE : 0 ≤ E) (hyE : y ^ 2 ≤ A * E)
    (hy : y ≤ (1 - εY) * A) (hα : α1 ^ 2 + α2 ^ 2 = 2 * B) (hβ : β1 ^ 2 + β2 ^ 2 ≤ 2 * A - 2 * E)
    (ha1 : 0 ≤ α1) (ha2 : 0 ≤ α2) (hb1 : 0 ≤ β1) (hb2 : 0 ≤ β2) :
    y + (α1 * β1 + α2 * β2) + α1 * α2 ≤ 1 - εY / 12 := by
  have hA : 11 / 12 ≤ A := by linarith
  have hαα : α1 * α2 ≤ B := by nlinarith [sq_nonneg (α1 - α2)]
  set c := α1 * β1 + α2 * β2
  set z := A - y
  have hz : εY * A ≤ z := by simp only [z]; linarith
  have hZ : 0 ≤ z - εY / 12 := by nlinarith
  have hc2 : c ^ 2 ≤ 2 * B * (2 * A - 2 * E) := by
    have : c ^ 2 ≤ (α1 ^ 2 + α2 ^ 2) * (β1 ^ 2 + β2 ^ 2) := by
      nlinarith [sq_nonneg (α1 * β2 - α2 * β1)]
    rw [hα] at this
    exact this.trans (mul_le_mul_of_nonneg_left hβ (by linarith))
  have hAE : A - E ≤ 2 * z := by
    have h1 : A * (A - E) ≤ A * (2 * z) := by nlinarith [sq_nonneg (A - y)]
    exact le_of_mul_le_mul_left h1 (by linarith)
  have hc2' : c ^ 2 ≤ (z - εY / 12) ^ 2 := by
    have h1 : c ^ 2 ≤ 8 * B * z := by nlinarith
    have h2 : 8 * B * z ≤ 2 / 3 * εY * z := by nlinarith
    have h3 : 2 / 3 * εY * z ≤ (z - εY / 12) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 (show 11 / 12 * εY ≤ z by nlinarith)) hεY0.le]
    linarith
  have hc : c ≤ z - εY / 12 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  simp only [z] at hc
  linarith

set_option maxHeartbeats 1000000 in
/-- The Y-step: if `1 - ‖d‖² ≤ εY/12` then `Re⟨u, Yv⟩ ≤ 1 - εY/12`. -/
theorem ystep (P Y : E →L[ℂ] E) (hPP : P * P = P) (hPadj : ContinuousLinearMap.adjoint P = P)
    (hY1 : ‖Y‖ ≤ 1) (εY : ℝ) (hεY0 : 0 < εY) (hεY1 : εY ≤ 1)
    (hY' : ‖P * Y * P‖ ≤ 1 - εY) (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hB : 1 - ‖(1 / 2 : ℂ) • (P u + P v)‖ ^ 2 ≤ εY / 12) :
    RCLike.re ⟪u, Y v⟫_ℂ ≤ 1 - εY / 12 := by
  set d := (1 / 2 : ℂ) • (P u + P v) with hd
  set Ys := ContinuousLinearMap.adjoint Y
  have hYs1 : ‖Ys‖ ≤ 1 := by rw [ContinuousLinearMap.adjoint.norm_map]; exact hY1
  have hPd : P d = d := by simp [hd, map_add, P_idem P hPP hPadj]
  have hadj : ∀ a b, ⟪P a, b⟫_ℂ = ⟪a, P b⟫_ℂ := P_adj P hPP hPadj
  have hYs : ∀ a b, ⟪Ys a, b⟫_ℂ = ⟪a, Y b⟫_ℂ := fun a b => ContinuousLinearMap.adjoint_inner_left Y b a
  set w := Y d + Ys d
  set e := (1 / 2 : ℂ) • P w with he
  set A := ‖d‖ ^ 2
  set B := 1 - A
  set E' := ‖e‖ ^ 2
  set y := RCLike.re ⟪d, Y d⟫_ℂ
  -- the four norms
  have hα : ‖u - d‖ ^ 2 + ‖v - d‖ ^ 2 = 2 * B := by
    have hud : RCLike.re ⟪u, d⟫_ℂ + RCLike.re ⟪v, d⟫_ℂ = 2 * A := by
      have h1 : ⟪u, d⟫_ℂ + ⟪v, d⟫_ℂ = ⟪P u + P v, d⟫_ℂ := by
        rw [← inner_add_left]
        conv_lhs => rw [← hPd]
        rw [← hadj, map_add]
      have h2 : P u + P v = (2 : ℂ) • d := by
        rw [hd, smul_smul]; norm_num
      have h3 : RCLike.re ⟪(2 : ℂ) • d, d⟫_ℂ = 2 * RCLike.re ⟪d, d⟫_ℂ := by
        rw [inner_smul_left]; simp
      rw [← map_add, h1, h2, h3, inner_self_eq_norm_sq]
    rw [@norm_sub_sq ℂ, @norm_sub_sq ℂ, hu, hv]
    simp only [B]
    linarith
  -- the projection of `w` and the vector `e`
  have hPe : P e = e := by simp [he, P_idem P hPP hPadj]
  have hwe : RCLike.re ⟪w, e⟫_ℂ = 2 * E' := by
    have : ⟪w, e⟫_ℂ = (1 / 2 : ℂ) * ⟪P w, P w⟫_ℂ := by
      rw [he, inner_smul_right, hadj, P_idem P hPP hPadj]
    have hE : E' = ‖P w‖ ^ 2 / 4 := by
      simp only [E', he, norm_smul]; norm_num; ring
    rw [this, inner_self_eq_norm_sq_to_K, hE]
    simp [div_eq_inv_mul]
    norm_cast
    ring
  have hβ : ‖Y d - e‖ ^ 2 + ‖Ys d - e‖ ^ 2 ≤ 2 * A - 2 * E' := by
    rw [@norm_sub_sq ℂ, @norm_sub_sq ℂ]
    have h1 : RCLike.re ⟪Y d, e⟫_ℂ + RCLike.re ⟪Ys d, e⟫_ℂ = 2 * E' := by
      rw [← map_add, ← inner_add_left]; exact hwe
    have h2 : ‖Y d‖ ^ 2 ≤ A := by
      have := Y.le_opNorm d
      have h' : ‖Y d‖ ≤ ‖d‖ := this.trans (by nlinarith [norm_nonneg d])
      simp only [A]; exact pow_le_pow_left₀ (norm_nonneg _) h' 2
    have h3 : ‖Ys d‖ ^ 2 ≤ A := by
      have := Ys.le_opNorm d
      have h' : ‖Ys d‖ ≤ ‖d‖ := this.trans (by nlinarith [norm_nonneg d])
      simp only [A]; exact pow_le_pow_left₀ (norm_nonneg _) h' 2
    simp only [E'] at h1 ⊢
    linarith
  have hde : RCLike.re ⟪d, e⟫_ℂ = y := by
    have : ⟪d, e⟫_ℂ = (1 / 2 : ℂ) * (⟪d, Y d⟫_ℂ + ⟪d, Ys d⟫_ℂ) := by
      rw [he, inner_smul_right, ← hadj, hPd, inner_add_right]
    rw [this]
    have h2 : ⟪d, Ys d⟫_ℂ = (starRingEnd ℂ) ⟪d, Y d⟫_ℂ := by
      rw [← inner_conj_symm, hYs]
    rw [h2, Complex.add_conj]
    simp only [y]
    rw [show (1 / 2 : ℂ) * ((2 * (⟪d, Y d⟫_ℂ).re : ℝ) : ℂ) = (((⟪d, Y d⟫_ℂ).re : ℝ) : ℂ) by push_cast; ring]
    rfl
  have hyE : y ^ 2 ≤ A * E' := by
    rw [← hde]
    have := (RCLike.abs_re_le_norm ⟪d, e⟫_ℂ).trans (norm_inner_le_norm d e)
    have h0 : 0 ≤ ‖d‖ * ‖e‖ := by positivity
    have := sq_le_sq' (by linarith [abs_le.1 this |>.1, neg_abs_le (RCLike.re ⟪d, e⟫_ℂ)]) (le_trans (le_abs_self _) this)
    simp only [A, E']
    nlinarith
  have hy : y ≤ (1 - εY) * A := by
    have h1 : ⟪d, Y d⟫_ℂ = ⟪d, (P * Y * P) d⟫_ℂ := by
      simp only [ContinuousLinearMap.mul_apply, hPd]
      rw [← hadj, hPd]
    have h2 := (RCLike.re_le_norm ⟪d, (P * Y * P) d⟫_ℂ).trans (norm_inner_le_norm d _)
    have h3 : ‖d‖ * ‖(P * Y * P) d‖ ≤ ‖d‖ * ((1 - εY) * ‖d‖) :=
      mul_le_mul_of_nonneg_left (((P * Y * P).le_opNorm d).trans
        (mul_le_mul_of_nonneg_right hY' (norm_nonneg _))) (norm_nonneg _)
    simp only [y, A, h1]
    nlinarith
  -- decomposition of `⟪u, Y v⟫`
  have hsum0 : ⟪u - d + (v - d), e⟫_ℂ = 0 := by
    rw [← hPe, ← hadj]
    have : P (u - d + (v - d)) = 0 := by
      rw [map_add, map_sub, map_sub, hPd]
      have : P u + P v = (2 : ℂ) • d := by rw [hd, smul_smul]; norm_num
      rw [show P u - d + (P v - d) = (P u + P v) - (2 : ℂ) • d by rw [two_smul]; abel, this, sub_self]
    rw [this, inner_zero_left]
  have hdec : RCLike.re ⟪u, Y v⟫_ℂ = y + (RCLike.re ⟪u - d, Y d - e⟫_ℂ + RCLike.re ⟪v - d, Ys d - e⟫_ℂ) +
      RCLike.re ⟪u - d, Y (v - d)⟫_ℂ := by
    have h1 : ⟪u, Y v⟫_ℂ = ⟪d, Y d⟫_ℂ + ⟪u - d, Y d⟫_ℂ + ⟪d, Y (v - d)⟫_ℂ + ⟪u - d, Y (v - d)⟫_ℂ := by
      have hu' : u = d + (u - d) := by abel
      have hv' : v = d + (v - d) := by abel
      conv_lhs => rw [hu', hv']
      rw [map_add, inner_add_left, inner_add_right, inner_add_right]
      ring
    have h2 : RCLike.re ⟪d, Y (v - d)⟫_ℂ = RCLike.re ⟪v - d, Ys d⟫_ℂ := by
      rw [← hYs, ← inner_conj_symm, RCLike.conj_re]
    have h3 : RCLike.re ⟪u - d, e⟫_ℂ + RCLike.re ⟪v - d, e⟫_ℂ = 0 := by
      rw [← map_add, ← inner_add_left, hsum0, map_zero]
    have h4 : RCLike.re ⟪u - d, Y d - e⟫_ℂ = RCLike.re ⟪u - d, Y d⟫_ℂ - RCLike.re ⟪u - d, e⟫_ℂ := by
      rw [inner_sub_right, map_sub]
    have h5 : RCLike.re ⟪v - d, Ys d - e⟫_ℂ = RCLike.re ⟪v - d, Ys d⟫_ℂ - RCLike.re ⟪v - d, e⟫_ℂ := by
      rw [inner_sub_right, map_sub]
    rw [h1, map_add, map_add, map_add, h2, h4, h5]
    simp only [y]
    linarith
  -- bounds on the pieces
  have hc1 : RCLike.re ⟪u - d, Y d - e⟫_ℂ ≤ ‖u - d‖ * ‖Y d - e‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hc2 : RCLike.re ⟪v - d, Ys d - e⟫_ℂ ≤ ‖v - d‖ * ‖Ys d - e‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hc3 : RCLike.re ⟪u - d, Y (v - d)⟫_ℂ ≤ ‖u - d‖ * ‖v - d‖ := by
    refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    exact mul_le_mul_of_nonneg_left ((Y.le_opNorm _).trans (by nlinarith [norm_nonneg (v - d)]))
      (norm_nonneg _)
  have hfin := ystep_alg A B E' y ‖u - d‖ ‖v - d‖ ‖Y d - e‖ ‖Ys d - e‖ εY hεY0 hεY1
    (by simp only [B]; ring) hB (by
      have hpu := pyth P hPP hPadj u
      have hpv := pyth P hPP hPadj v
      rw [hu] at hpu; rw [hv] at hpv
      have hPu : ‖P u‖ ≤ 1 := by nlinarith [norm_nonneg (P u), norm_nonneg (u - P u)]
      have hPv : ‖P v‖ ≤ 1 := by nlinarith [norm_nonneg (P v), norm_nonneg (v - P v)]
      have hdn : ‖d‖ ≤ 1 := by
        rw [hd, norm_smul]
        have := norm_add_le (P u) (P v)
        norm_num
        linarith
      simp only [B, A]
      nlinarith [norm_nonneg d]) (sq_nonneg _) hyE hy hα hβ
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  rw [hdec]
  linarith

theorem unit_bound (P X Y : E →L[ℂ] E) (hPP : P * P = P) (hPadj : ContinuousLinearMap.adjoint P = P)
    (hX1 : ‖X‖ ≤ 1) (hY1 : ‖Y‖ ≤ 1) (εX εY : ℝ) (hεX0 : 0 < εX) (hεX1 : εX ≤ 1)
    (hεY0 : 0 < εY) (hεY1 : εY ≤ 1) (hPX : P * X = P) (hXP : X * P = P)
    (hX' : ‖(1 - P) * X * (1 - P)‖ ≤ 1 - εX) (hY' : ‖P * Y * P‖ ≤ 1 - εY)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    RCLike.re ⟪u, ((p : ℂ) • X + ((1 - p : ℝ) : ℂ) • Y) v⟫_ℂ ≤ 1 - εY / 12 * min (p * εX) (1 - p) := by
  have hsplit : RCLike.re ⟪u, ((p : ℂ) • X + ((1 - p : ℝ) : ℂ) • Y) v⟫_ℂ =
      p * RCLike.re ⟪u, X v⟫_ℂ + (1 - p) * RCLike.re ⟪u, Y v⟫_ℂ := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_right,
      inner_smul_right, map_add]
    simp
  rw [hsplit]
  have hYb : RCLike.re ⟪u, Y v⟫_ℂ ≤ 1 := by
    refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [hu, one_mul]
    exact (Y.le_opNorm v).trans (by rw [hv, mul_one]; exact hY1)
  have hXb : RCLike.re ⟪u, X v⟫_ℂ ≤ 1 := by
    refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [hu, one_mul]
    exact (X.le_opNorm v).trans (by rw [hv, mul_one]; exact hX1)
  have hmin1 : min (p * εX) (1 - p) ≤ p * εX := min_le_left _ _
  have hmin2 : min (p * εX) (1 - p) ≤ 1 - p := min_le_right _ _
  by_cases hD : εY / 12 ≤ 1 - ‖(1 / 2 : ℂ) • (P u + P v)‖ ^ 2
  · have hx := xstep P X hPP hPadj hPX hXP εX hεX1 hX' u v hu hv
    have : RCLike.re ⟪u, X v⟫_ℂ ≤ 1 - εX * (εY / 12) := hx.trans (by nlinarith)
    nlinarith
  · push Not at hD
    have hy := ystep P Y hPP hPadj hY1 εY hεY0 hεY1 hY' u v hu hv hD.le
    nlinarith

theorem clm_bound (P X Y : E →L[ℂ] E) (hPP : P * P = P) (hPadj : ContinuousLinearMap.adjoint P = P)
    (hX1 : ‖X‖ ≤ 1) (hY1 : ‖Y‖ ≤ 1) (εX εY : ℝ) (hεX0 : 0 < εX) (hεX1 : εX ≤ 1)
    (hεY0 : 0 < εY) (hεY1 : εY ≤ 1) (hPX : P * X = P) (hXP : X * P = P)
    (hX' : ‖(1 - P) * X * (1 - P)‖ ≤ 1 - εX) (hY' : ‖P * Y * P‖ ≤ 1 - εY)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ‖(p : ℂ) • X + ((1 - p : ℝ) : ℂ) • Y‖ ≤ 1 - εY / 12 * min (p * εX) (1 - p) := by
  set T := (p : ℂ) • X + ((1 - p : ℝ) : ℂ) • Y
  set c := 1 - εY / 12 * min (p * εX) (1 - p)
  have hc : 0 ≤ c := by
    have : min (p * εX) (1 - p) ≤ 1 - p := min_le_right _ _
    have : 0 ≤ min (p * εX) (1 - p) := le_min (by positivity) (by linarith)
    simp only [c]; nlinarith
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  by_cases hTv : T v = 0
  · rw [hTv, norm_zero]; positivity
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hTn : 0 < ‖T v‖ := norm_pos_iff.2 hTv
  set v' := ((‖v‖⁻¹ : ℝ) : ℂ) • v
  set u' := ((‖T v‖⁻¹ : ℝ) : ℂ) • T v
  have hv' : ‖v'‖ = 1 := by
    simp only [v', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    field_simp
  have hu' : ‖u'‖ = 1 := by
    simp only [u', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    field_simp
  have key := unit_bound P X Y hPP hPadj hX1 hY1 εX εY hεX0 hεX1 hεY0 hεY1 hPX hXP hX' hY' p hp0 hp1
    u' v' hu' hv'
  have : RCLike.re ⟪u', T v'⟫_ℂ = ‖T v‖ / ‖v‖ := by
    simp only [u', v', map_smul, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp only [Complex.conj_ofReal]
    norm_cast
    field_simp
    simp only [← Complex.ofReal_mul, RCLike.re_to_complex]
    rw [Complex.re_ofReal_mul]
    show ‖v‖ * (1 / ‖v‖ * (1 / ‖T v‖) * (‖T v‖ ^ 2)) = ‖T v‖
    field_simp
  rw [this] at key
  rwa [div_le_iff₀ hvn] at key

end DepthOneQExp.HH09Aux

open scoped Matrix.Norms.L2Operator in
open DepthOneQExp.HH09Aux in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (P X Y : Matrix ι ι ℂ)
    (hP2 : P * P = P) (hPh : P.IsHermitian) (hXn : ‖X‖ ≤ 1) (hYn : ‖Y‖ ≤ 1)
    (εX εY : ℝ) (hεX : εX ∈ Set.Ioc (0 : ℝ) 1) (hεY : εY ∈ Set.Ioc (0 : ℝ) 1)
    (hPX : P * X = P) (hXP : X * P = P)
    (hX' : ‖(1 - P) * X * (1 - P)‖ ≤ 1 - εX) (hY' : ‖P * Y * P‖ ≤ 1 - εY)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(p : ℂ) • X + ((1 - p : ℝ) : ℂ) • Y‖ ≤ 1 - εY / 12 * min (p * εX) (1 - p) := by
  let φ := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
  have hn : ∀ A : Matrix ι ι ℂ, ‖φ A‖ = ‖A‖ := fun A => Matrix.l2_opNorm_toEuclideanCLM A
  have hPadj : ContinuousLinearMap.adjoint (φ P) = φ P := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    congr 1
  have := clm_bound (φ P) (φ X) (φ Y) (by rw [← map_mul, hP2]) hPadj (by rw [hn]; exact hXn)
    (by rw [hn]; exact hYn) εX εY hεX.1 hεX.2 hεY.1 hεY.2 (by rw [← map_mul, hPX])
    (by rw [← map_mul, hXP]) (by rw [← map_one φ, ← map_sub, ← map_mul, ← map_mul, hn]; exact hX')
    (by rw [← map_mul, ← map_mul, hn]; exact hY') p hp.1 hp.2
  rw [← map_smul, ← map_smul, ← map_add, hn] at this
  exact this
