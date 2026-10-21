-- Prove2me | solution 1 for CoProdBundle.Equil.eq_4c_best_response
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:04:07.154765+00:00
-- url     : https://prove2.me/submissions/ed5c000e-ffec-4d92-8b74-eaf8b0e7a31a

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

set_option autoImplicit false
open CoProdBundle.Equil

lemma rpow32_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (3/2 : ℝ) = (Real.sqrt x) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma surplus_le (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 ≤ Q) (P : ℝ) :
    surplus A b w θ Q P ≤ (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ) := by
  have hq : 0 ≤ Q ^ θ := Real.rpow_nonneg hQ θ
  have hM : 0 ≤ (A - b * w) / 3 * Q ^ θ := by positivity
  rw [rpow32_eq hM]
  set t := Real.sqrt ((A - b * w) / 3 * Q ^ θ) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = (A - b * w) / 3 * Q ^ θ := Real.sq_sqrt hM
  unfold surplus demand
  set u := A * Q ^ θ - b * P with hu
  by_cases hu0 : u ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos hu0]
    have : 0 ≤ (2 / b) * t ^ 3 := by positivity
    simpa using this
  · push_neg at hu0
    set s := Real.sqrt u with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
    have hP : b * P = A * Q ^ θ - s ^ 2 := by rw [hs2, hu]; ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    have e : (P - w * Q ^ θ) * s * b = (3 * t ^ 2 - s ^ 2) * s := by
      linear_combination s * hP - 3 * s * ht2
    have e2 : (P - w * Q ^ θ) * s * b = (P - w * Q ^ θ) * s * b := rfl
    nlinarith [mul_nonneg (sq_nonneg (t - s)) (by linarith : 0 ≤ 2 * t + s)]

lemma Pstar_demand (A b w θ Q : ℝ) (hb : 0 < b) (hQ : 0 ≤ Q) :
    demand A b θ (Pstar A b w θ Q) Q = Real.sqrt ((A - b * w) / 3 * Q ^ θ) := by
  unfold demand Pstar
  congr 1
  field_simp
  ring

lemma surplus_Pstar (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 ≤ Q) :
    surplus A b w θ Q (Pstar A b w θ Q) = (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ) := by
  have hq : 0 ≤ Q ^ θ := Real.rpow_nonneg hQ θ
  have hM : 0 ≤ (A - b * w) / 3 * Q ^ θ := by positivity
  rw [rpow32_eq hM]
  unfold surplus
  rw [Pstar_demand A b w θ Q hb hQ]
  set t := Real.sqrt ((A - b * w) / 3 * Q ^ θ) with ht
  have ht2 : t ^ 2 = (A - b * w) / 3 * Q ^ θ := Real.sq_sqrt hM
  unfold Pstar
  field_simp
  linear_combination (-6 * t) * ht2

lemma Pstar_unique (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 < Q) (P : ℝ)
    (hP : surplus A b w θ Q P = (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ)) :
    P = Pstar A b w θ Q := by
  have hq : 0 < Q ^ θ := Real.rpow_pos_of_pos hQ θ
  have hM : 0 < (A - b * w) / 3 * Q ^ θ := by positivity
  rw [rpow32_eq hM.le] at hP
  set t := Real.sqrt ((A - b * w) / 3 * Q ^ θ) with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hM
  have ht2 : t ^ 2 = (A - b * w) / 3 * Q ^ θ := Real.sq_sqrt hM.le
  unfold surplus demand at hP
  set u := A * Q ^ θ - b * P with hu
  by_cases hu0 : u ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos hu0] at hP
    simp at hP
    exfalso
    rcases hP with h | h
    · exact hb.ne' h
    · exact ht0.ne' h
  · push_neg at hu0
    set s := Real.sqrt u with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hu0
    have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
    have hPb : b * P = A * Q ^ θ - s ^ 2 := by rw [hs2, hu]; ring
    rw [div_mul_eq_mul_div, eq_div_iff hb.ne'] at hP
    have e : (P - w * Q ^ θ) * s * b = (3 * t ^ 2 - s ^ 2) * s := by
      linear_combination s * hPb - 3 * s * ht2
    have h3 : (t - s) ^ 2 * (2 * t + s) = 0 := by nlinarith
    have h4 : (t - s) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · linarith
    have h5 : s = t := by nlinarith [sq_nonneg (t - s)]
    have h6 : u = (A - b * w) / 3 * Q ^ θ := by rw [← hs2, h5, ht2]
    unfold Pstar
    rw [hu] at h6
    field_simp
    nlinarith [h6]

lemma S_eq (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 ≤ Q) :
    S A b w θ Q = (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ) := by
  unfold S
  apply le_antisymm
  · exact ciSup_le fun P => surplus_le A b w θ Q hb hAw hQ P
  · refine le_ciSup_of_le ⟨(2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ), ?_⟩
      (Pstar A b w θ Q) (surplus_Pstar A b w θ Q hb hAw hQ).ge
    rintro _ ⟨P, rfl⟩
    exact surplus_le A b w θ Q hb hAw hQ P

lemma S_fac (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 < Q) :
    S A b w θ Q = (2 / b) * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) := by
  rw [S_eq A b w θ Q hb hAw hQ.le, Real.mul_rpow (by positivity) (Real.rpow_nonneg hQ.le θ),
    ← Real.rpow_mul hQ.le]
  congr 3; ring

lemma Y_eq (A b w θ Q : ℝ) (hAw : 0 < A - b * w) (hQ : 0 < Q) :
    ((1 / Q ^ θ) * (3 / (A - b * w))) ^ (3 / 2 : ℝ) =
      1 / (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) := by
  have hq : 0 < Q ^ θ := Real.rpow_pos_of_pos hQ θ
  have e : (1 / Q ^ θ) * (3 / (A - b * w)) = (((A - b * w) / 3) * Q ^ θ)⁻¹ := by
    field_simp
  rw [e, Real.inv_rpow (by positivity), Real.mul_rpow (by positivity) hq.le,
    ← Real.rpow_mul hQ.le, one_div]
  congr 3; ring

lemma br_eq (γ A b w θ ci Q : ℝ) (hAw : 0 < A - b * w) (hQ : 0 < Q) :
    br4c γ A b w θ ci Q =
      (2 - ci * (b * Q / (γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2))))) *
        (Q / (2 - 3 * θ)) := by
  unfold br4c
  rw [Y_eq A b w θ Q hAw hQ]
  congr 2
  field_simp

lemma Q_iff (a M θ Q : ℝ) (ha : 0 < a) (hM : 0 < M) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3)
    (hQ : 0 < Q) :
    Q / (a ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) = M ↔
      Q = M ^ (2 / (2 - 3 * θ)) * a ^ (3 / (2 - 3 * θ)) := by
  have hα : 0 < (2 - 3 * θ) / 2 := by linarith
  have hE : 0 < Q ^ (3 * θ / 2) := Real.rpow_pos_of_pos hQ _
  have ha32 : 0 < a ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
  have hQE : Q / Q ^ (3 * θ / 2) = Q ^ ((2 - 3 * θ) / 2) := by
    have := Real.rpow_sub hQ 1 (3 * θ / 2)
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  have h1 : Q / (a ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) = M ↔
      Q ^ ((2 - 3 * θ) / 2) = M * a ^ (3 / 2 : ℝ) := by
    rw [← hQE, div_eq_iff (by positivity)]
    constructor <;> intro h <;> [skip; skip] <;> field_simp at * <;> linarith
  rw [h1]
  have hinv : ((2 - 3 * θ) / 2)⁻¹ = 2 / (2 - 3 * θ) := by
    rw [inv_div]
  constructor
  · intro h
    have : Q = (Q ^ ((2 - 3 * θ) / 2)) ^ (((2 - 3 * θ) / 2)⁻¹) :=
      (Real.rpow_rpow_inv hQ.le hα.ne').symm
    rw [this, h, Real.mul_rpow hM.le ha32.le, ← Real.rpow_mul ha.le, hinv]
    congr 2
    field_simp
  · intro h
    rw [h, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hM.le,
      ← Real.rpow_mul ha.le]
    have hne : 2 - 3 * θ ≠ 0 := ne_of_gt (by linarith)
    have e1 : 2 / (2 - 3 * θ) * ((2 - 3 * θ) / 2) = 1 := by field_simp
    have e2 : 3 / (2 - 3 * θ) * ((2 - 3 * θ) / 2) = 3 / 2 := by field_simp
    rw [e1, e2, Real.rpow_one]

lemma card_lt {I : ℕ} (k : ℕ) (hk : k ≤ I) :
    (Finset.univ.filter (fun i : Fin I => (i : ℕ) < k)).card = k := by
  have := @Fin.card_filter_val_lt I k
  simpa [min_eq_right hk] using this

lemma rpow_half (θ Q : ℝ) (hQ : 0 < Q) :
    Q ^ ((2 - 3 * θ) / 2) = Q / Q ^ (3 * θ / 2) := by
  have := Real.rpow_sub hQ 1 (3 * θ / 2)
  rw [Real.rpow_one] at this
  rw [← this]; congr 1; ring

lemma Bform (γ A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 < Q) :
    2 * γ / (b * Q ^ ((2 - 3 * θ) / 2)) * ((A - b * w) / 3) ^ (3 / 2 : ℝ) =
      2 * γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) / (b * Q) := by
  have hE : 0 < Q ^ (3 * θ / 2) := Real.rpow_pos_of_pos hQ _
  rw [rpow_half θ Q hQ]
  field_simp

lemma Bform_S (γ A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 < Q) :
    2 * γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) / (b * Q) =
      γ * S A b w θ Q / Q := by
  rw [S_fac A b w θ Q hb hAw hQ]
  field_simp

lemma br_nonneg_iff (γ A b w θ ci Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hQ : 0 < Q) :
    0 ≤ br4c γ A b w θ ci Q ↔
      ci ≤ 2 * γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) / (b * Q) := by
  have hE : 0 < Q ^ (3 * θ / 2) := Real.rpow_pos_of_pos hQ _
  have ha : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  rw [br_eq γ A b w θ ci Q hAw hQ]
  have h23 : 0 < Q / (2 - 3 * θ) := div_pos hQ (by linarith)
  rw [mul_nonneg_iff_of_pos_right h23, sub_nonneg]
  have hZ : 0 < b * Q / (γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2))) := by positivity
  rw [← le_div_iff₀ hZ]
  have : 2 / (b * Q / (γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)))) =
      2 * γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) / (b * Q) := by
    field_simp
  rw [this]

lemma br_pos_iff (γ A b w θ ci Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hQ : 0 < Q) :
    0 < br4c γ A b w θ ci Q ↔
      ci < 2 * γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) / (b * Q) := by
  have hE : 0 < Q ^ (3 * θ / 2) := Real.rpow_pos_of_pos hQ _
  have ha : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  rw [br_eq γ A b w θ ci Q hAw hQ]
  have h23 : 0 < Q / (2 - 3 * θ) := div_pos hQ (by linarith)
  rw [mul_pos_iff_of_pos_right h23, sub_pos]
  have hZ : 0 < b * Q / (γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2))) := by positivity
  rw [← lt_div_iff₀ hZ]
  have : 2 / (b * Q / (γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)))) =
      2 * γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) / (b * Q) := by
    field_simp
  rw [this]


lemma inv_one_add_ge (t : ℝ) (ht : 0 < 1 + t) : 1 - t ≤ 1 / (1 + t) := by
  rw [le_div_iff₀ ht]; nlinarith [sq_nonneg t]

lemma tangent_alg (β R x y Y Q p r u v K0 c : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 ≤ R)
    (hx : 0 < x) (hy : 0 ≤ y) (hK0 : 0 < K0) (hQd : Q = x + R) (hYd : Y = y + R)
    (hp : 0 < p) (hr : 0 < r) (hu : 0 < u) (hv : 0 < v) (hpr : p * r = Q) (huv : u * v = Y)
    (hub : u ≤ p * (1 + β * (Y / Q - 1))) (hvb : v ≤ r * (1 + (1 - β) * (Y / Q - 1)))
    (hc : c = K0 * p * (R + β * x) / Q ^ 2) :
    K0 * (y / Y) * u - c * y ≤ K0 * (x / Q) * p - c * x := by
  have hQ : 0 < Q := by rw [hQd]; linarith
  have hY : 0 < Y := by rw [← huv]; positivity
  set s := Y / Q - 1 with hs
  have hs1 : -1 < s := by
    have : 0 < Y / Q := by positivity
    linarith
  have hα : 0 < 1 - β := by linarith
  have hpos : 0 < 1 + (1 - β) * s := by nlinarith
  have h1 : y / Y * u = u - R / v := by
    have : y = Y - R := by rw [hYd]; ring
    rw [this]
    field_simp
    rw [← huv]; ring
  have h2 : (R / r) * (1 - (1 - β) * s) ≤ R / v := by
    have h3 : R / (r * (1 + (1 - β) * s)) ≤ R / v :=
      div_le_div_of_nonneg_left hR hv (by linarith [hvb, mul_comm r (1 + (1 - β) * s)])
    refine le_trans ?_ h3
    have h4 := inv_one_add_ge ((1 - β) * s) hpos
    have h5 : R / (r * (1 + (1 - β) * s)) = R / r * (1 / (1 + (1 - β) * s)) := by
      field_simp
    rw [h5]
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have h3 : x / Q * p = p - R / r := by
    have : x = Q - R := by rw [hQd]; ring
    rw [this]
    have : r = Q / p := by rw [eq_div_iff hp.ne']; linarith
    rw [this]; field_simp
  have hsv : s = (y - x) / Q := by
    rw [hs, hYd, hQd]; field_simp; ring
  have hid : K0 * (p * β * s + R / r * (1 - β) * s) = c * (y - x) := by
    have : r = Q / p := by rw [eq_div_iff hp.ne']; linarith
    rw [hsv, hc, this]
    have hQx : x = Q - R := by rw [hQd]; ring
    field_simp
    rw [hQx]; ring
  have hmain : u - R / v ≤ p * (1 + β * s) - (R / r) * (1 - (1 - β) * s) := by
    linarith
  have hK : K0 * (u - R / v) ≤ K0 * (p * (1 + β * s) - (R / r) * (1 - (1 - β) * s)) :=
    mul_le_mul_of_nonneg_left hmain hK0.le
  calc K0 * (y / Y) * u - c * y = K0 * (y / Y * u) - c * y := by ring
    _ = K0 * (u - R / v) - c * y := by rw [h1]
    _ ≤ K0 * (p * (1 + β * s) - (R / r) * (1 - (1 - β) * s)) - c * y := by linarith
    _ = K0 * (p - R / r) - c * x + (K0 * (p * β * s + R / r * (1 - β) * s) - c * (y - x)) := by ring
    _ = K0 * (x / Q) * p - c * x := by rw [hid]; linear_combination (-K0) * h3
lemma bern_bound (Y Q e : ℝ) (hY : 0 < Y) (hQ : 0 < Q) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Y ^ e ≤ Q ^ e * (1 + e * (Y / Q - 1)) := by
  have hs : -1 ≤ Y / Q - 1 := by
    have : 0 < Y / Q := by positivity
    linarith
  have h := rpow_one_add_le_one_add_mul_self hs he0 he1
  have e1 : 1 + (Y / Q - 1) = Y / Q := by ring
  rw [e1, Real.div_rpow hY.le hQ.le, div_le_iff₀ (Real.rpow_pos_of_pos hQ e)] at h
  linarith

lemma sufficiency (β R x y K0 c : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 ≤ R)
    (hx : 0 < x) (hy : 0 ≤ y) (hK0 : 0 < K0)
    (hc : c = K0 * (x + R) ^ β * (R + β * x) / (x + R) ^ 2) :
    K0 * (y / (y + R)) * (y + R) ^ β - c * y ≤ K0 * (x / (x + R)) * (x + R) ^ β - c * x := by
  have hQ : 0 < x + R := by linarith
  have hp : 0 < (x + R) ^ β := Real.rpow_pos_of_pos hQ β
  by_cases hY : y + R = 0
  · have hy0 : y = 0 := by linarith
    have hR0 : R = 0 := by linarith
    subst hy0 hR0
    simp only [add_zero, zero_div, mul_zero, zero_mul, sub_zero, div_self hx.ne', mul_one] at *
    have : c * x = K0 * x ^ β * β := by
      rw [hc, zero_add]; field_simp
    rw [this]
    nlinarith [mul_pos hK0 hp]
  · have hYp : 0 < y + R := lt_of_le_of_ne (by linarith) (Ne.symm hY)
    have hr : 0 < (x + R) ^ (1 - β) := Real.rpow_pos_of_pos hQ _
    have hu : 0 < (y + R) ^ β := Real.rpow_pos_of_pos hYp β
    have hv : 0 < (y + R) ^ (1 - β) := Real.rpow_pos_of_pos hYp _
    refine tangent_alg β R x y (y + R) (x + R) ((x + R) ^ β) ((x + R) ^ (1 - β))
      ((y + R) ^ β) ((y + R) ^ (1 - β)) K0 c hβ0 hβ1 hR hx hy hK0 rfl rfl hp hr hu hv ?_ ?_
      (bern_bound _ _ _ hYp hQ hβ0.le hβ1.le) ?_ hc
    · rw [← Real.rpow_add hQ]; simp
    · rw [← Real.rpow_add hYp]; simp
    · exact bern_bound _ _ _ hYp hQ (by linarith) (by linarith)
lemma necessity (β R x K0 c : ℝ) (hR : 0 ≤ R) (hx : 0 < x)
    (hmax : ∀ y : ℝ, 0 ≤ y →
      K0 * (y / (y + R)) * (y + R) ^ β - c * y ≤ K0 * (x / (x + R)) * (x + R) ^ β - c * x) :
    c = K0 * (x + R) ^ β * (R + β * x) / (x + R) ^ 2 := by
  have hQ : 0 < x + R := by linarith
  have hloc : IsLocalMax (fun y : ℝ => K0 * (y / (y + R)) * (y + R) ^ β - c * y) x := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hmax y (le_of_lt hy)
  have h1 : HasDerivAt (fun y : ℝ => y + R) 1 x := (hasDerivAt_id x).add_const R
  have h2 : HasDerivAt (fun y : ℝ => y / (y + R)) ((1 * (x + R) - x * 1) / (x + R) ^ 2) x :=
    (hasDerivAt_id x).div h1 hQ.ne'
  have h3 : HasDerivAt (fun y : ℝ => (y + R) ^ β) (1 * β * (x + R) ^ (β - 1)) x :=
    h1.rpow_const (Or.inl hQ.ne')
  have h4 := (((h2.const_mul K0).mul h3).sub ((hasDerivAt_id x).const_mul c))
  have h5 := hloc.hasDerivAt_eq_zero h4
  rw [Real.rpow_sub_one hQ.ne'] at h5
  field_simp at h5 ⊢
  nlinarith [h5]
lemma zero_best (β R K0 c : ℝ) (hR : 0 < R) (hc : c < K0 * R ^ β / R) :
    ∃ y : ℝ, 0 < y ∧ 0 < K0 * (y / (y + R)) * (y + R) ^ β - c * y := by
  have hcont : ContinuousAt (fun y : ℝ => K0 * (y + R) ^ β / (y + R)) 0 := by
    have h1 : ContinuousAt (fun y : ℝ => y + R) 0 := continuousAt_id.add continuousAt_const
    have h2 : ContinuousAt (fun y : ℝ => (y + R) ^ β) 0 :=
      h1.rpow_const (Or.inl (by simp [hR.ne']))
    exact (continuousAt_const.mul h2).div h1 (by simp [hR.ne'])
  have hev : ∀ᶠ y in nhds (0:ℝ), c < K0 * (y + R) ^ β / (y + R) :=
    continuousAt_const.eventually_lt hcont (by simpa using hc)
  obtain ⟨y, hy1, hy2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0))).exists
  refine ⟨y, hy2, ?_⟩
  have : K0 * (y / (y + R)) * (y + R) ^ β - c * y = y * (K0 * (y + R) ^ β / (y + R) - c) := by
    ring
  rw [this]
  exact mul_pos hy2 (by linarith)
lemma S_fac0 (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 ≤ Q) :
    S A b w θ Q = (2 / b) * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) := by
  rw [S_eq A b w θ Q hb hAw hQ, Real.mul_rpow (by positivity) (Real.rpow_nonneg hQ θ),
    ← Real.rpow_mul hQ]
  congr 3; ring

lemma total_update {I : ℕ} (q : Fin I → ℝ) (i : Fin I) (y : ℝ) :
    total (Function.update q i y) = y + (total q - q i) := by
  unfold total
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase Finset.univ q (Finset.mem_univ i)]
  ring

lemma R_nonneg {I : ℕ} (q : Fin I → ℝ) (hq : ∀ j, 0 ≤ q j) (i : Fin I) :
    0 ≤ total q - q i := by
  unfold total
  rw [← Finset.add_sum_erase Finset.univ q (Finset.mem_univ i)]
  have : 0 ≤ ∑ x ∈ Finset.univ.erase i, q x := Finset.sum_nonneg (fun j _ => hq j)
  linarith

lemma payoff_form (γ A b w θ : ℝ) {I : ℕ} (c q : Fin I → ℝ) (i : Fin I) (y : ℝ)
    (hb : 0 < b) (hAw : 0 < A - b * w) (hy : 0 ≤ y) (hR : 0 ≤ total q - q i) :
    payoff γ A b w θ c (Function.update q i y) i =
      (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (y / (y + (total q - q i))) *
        (y + (total q - q i)) ^ (3 * θ / 2) - c i * y := by
  unfold payoff
  rw [total_update, Function.update_self, S_fac0 A b w θ _ hb hAw (by linarith)]
  ring

lemma foc_iff (γ A b w θ ci R x : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hR : 0 ≤ R) (hx : 0 < x) :
    ci = (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (x + R) ^ (3 * θ / 2) *
      (R + 3 * θ / 2 * x) / (x + R) ^ 2 ↔ x = br4c γ A b w θ ci (x + R) := by
  have hQ : 0 < x + R := by linarith
  have hE : 0 < (x + R) ^ (3 * θ / 2) := Real.rpow_pos_of_pos hQ _
  have ha : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have h23 : 0 < 2 - 3 * θ := by linarith
  rw [br_eq γ A b w θ ci _ hAw hQ]
  set E := (x + R) ^ (3 * θ / 2)
  set κ := ((A - b * w) / 3) ^ (3 / 2 : ℝ)
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    field_simp at h
    field_simp
    nlinarith [h]

theorem solution (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (q : Fin I → ℝ) (hq : ∀ j, 0 ≤ q j) (i : Fin I) (x : ℝ) (hx : 0 < x) :
    (∀ y : ℝ, 0 ≤ y →
        payoff γ A b w θ c (Function.update q i y) i ≤ payoff γ A b w θ c (Function.update q i x) i) ↔
      x = br4c γ A b w θ (c i) (x + (total q - q i)) := by
  have hR := R_nonneg q hq i
  have hK0 : 0 < 2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ) := by
    have : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  constructor
  · intro h
    have hmax : ∀ y : ℝ, 0 ≤ y →
        (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (y / (y + (total q - q i))) *
          (y + (total q - q i)) ^ (3 * θ / 2) - c i * y ≤
        (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (x / (x + (total q - q i))) *
          (x + (total q - q i)) ^ (3 * θ / 2) - c i * x := by
      intro y hy
      have := h y hy
      rwa [payoff_form γ A b w θ c q i y hb hAw hy hR,
        payoff_form γ A b w θ c q i x hb hAw hx.le hR] at this
    exact (foc_iff γ A b w θ (c i) _ x hb hAw hθ0 hθ1 hγ0 hR hx).mp
      (necessity (3 * θ / 2) _ x _ (c i) hR hx hmax)
  · intro h y hy
    rw [payoff_form γ A b w θ c q i y hb hAw hy hR,
      payoff_form γ A b w θ c q i x hb hAw hx.le hR]
    exact sufficiency (3 * θ / 2) _ x y _ (c i) (by linarith) (by linarith) hR hx hy hK0
      ((foc_iff γ A b w θ (c i) _ x hb hAw hθ0 hθ1 hγ0 hR hx).mpr h)
