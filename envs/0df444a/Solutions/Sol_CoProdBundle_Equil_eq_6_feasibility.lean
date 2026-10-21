-- Prove2me | solution 1 for CoProdBundle.Equil.eq_6_feasibility
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:56:08.267433+00:00
-- url     : https://prove2.me/submissions/81e002a9-6cf3-4b39-8243-2de1a8bd737b

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

lemma psum_pos {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (k : ℕ) (hk1 : 1 ≤ k) (hkI : k ≤ I) :
    0 < psum c k := by
  unfold psum
  apply Finset.sum_pos (fun i _ => hc0 i)
  exact ⟨⟨0, by omega⟩, by simp; omega⟩

lemma sum_br {I : ℕ} (c : Fin I → ℝ) (γ A b w θ Q : ℝ) (hAw : 0 < A - b * w) (hQ : 0 < Q)
    (k : ℕ) (hkI : k ≤ I) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin I => (i : ℕ) < k), br4c γ A b w θ (c i) Q =
      (2 * k - psum c k * (b * Q / (γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2))))) *
        (Q / (2 - 3 * θ)) := by
  rw [Finset.sum_congr rfl (fun i _ => br_eq γ A b w θ (c i) Q hAw hQ), ← Finset.sum_mul,
    Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, card_lt k hkI,
    nsmul_eq_mul]
  unfold psum
  ring

lemma five_b_iff {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ Q : ℝ)
    (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ)
    (k : ℕ) (hk1 : 1 ≤ k) (hkI : k ≤ I) (hQ : 0 < Q) :
    (Q = ∑ i ∈ Finset.univ.filter (fun i : Fin I => (i : ℕ) < k), br4c γ A b w θ (c i) Q ↔
      Q / (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) =
        (γ / (b * (psum c k / k))) * (2 - (2 - 3 * θ) / k)) := by
  have hE : 0 < Q ^ (3 * θ / 2) := Real.rpow_pos_of_pos hQ _
  have ha : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hS : 0 < psum c k := psum_pos c hc0 k hk1 hkI
  have hk : (0:ℝ) < k := by exact_mod_cast hk1
  have h23 : 0 < 2 - 3 * θ := by linarith
  rw [sum_br c γ A b w θ Q hAw hQ k hkI]
  set W := Q / (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2)) with hW
  have hZ : b * Q / (γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2))) = b / γ * W := by
    rw [hW]; field_simp
  rw [hZ]
  have hM : (γ / (b * (psum c k / k))) * (2 - (2 - 3 * θ) / k) =
      γ * (2 * k - (2 - 3 * θ)) / (b * psum c k) := by
    field_simp
  rw [hM, eq_div_iff (by positivity)]
  constructor
  · intro h
    have h' : (2 - 3 * θ) = 2 * k - psum c k * (b / γ * W) := by
      have : Q * (2 - 3 * θ) = Q * (2 * k - psum c k * (b / γ * W)) := by
        field_simp at h ⊢
        linarith
      exact mul_left_cancel₀ hQ.ne' this
    field_simp at h' ⊢
    nlinarith [h']
  · intro h
    have h' : (2 - 3 * θ) = 2 * k - psum c k * (b / γ * W) := by
      field_simp at h ⊢
      nlinarith [h]
    field_simp
    nlinarith [h']

lemma M_pos {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ b θ : ℝ) (hb : 0 < b)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (k : ℕ) (hk1 : 1 ≤ k) (hkI : k ≤ I) :
    0 < (γ / (b * (psum c k / k))) * (2 - (2 - 3 * θ) / k) := by
  have hS : 0 < psum c k := psum_pos c hc0 k hk1 hkI
  have hk : (0:ℝ) < k := by exact_mod_cast hk1
  have : (2 - 3 * θ) / k ≤ 2 - 3 * θ := by
    apply div_le_self (by linarith) (by exact_mod_cast hk1)
  have h2 : 0 < 2 - (2 - 3 * θ) / k := by nlinarith
  positivity

lemma Q5c_pos {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ : ℝ) (hb : 0 < b)
    (hAw : 0 < A - b * w) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (k : ℕ) (hk1 : 1 ≤ k)
    (hkI : k ≤ I) : 0 < Q5c γ A b w θ c k := by
  have hM := M_pos c hc0 γ b θ hb hθ0 hθ1 hγ0 k hk1 hkI
  unfold Q5c
  have : 0 < (A - b * w) / 3 := by positivity
  positivity

lemma Q5c_W {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ : ℝ) (hb : 0 < b)
    (hAw : 0 < A - b * w) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (k : ℕ) (hk1 : 1 ≤ k)
    (hkI : k ≤ I) :
    Q5c γ A b w θ c k / (((A - b * w) / 3) ^ (3 / 2 : ℝ) * (Q5c γ A b w θ c k) ^ (3 * θ / 2)) =
      (γ / (b * (psum c k / k))) * (2 - (2 - 3 * θ) / k) :=
  (Q_iff ((A - b * w) / 3) _ θ _ (by positivity) (M_pos c hc0 γ b θ hb hθ0 hθ1 hγ0 k hk1 hkI)
    hθ0 hθ1 (Q5c_pos c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 k hk1 hkI)).mpr rfl

lemma ratio_Q5c {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ : ℝ) (hb : 0 < b)
    (hAw : 0 < A - b * w) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (k : ℕ) (hk1 : 1 ≤ k)
    (hkI : k ≤ I) :
    γ * S A b w θ (Q5c γ A b w θ c k) / Q5c γ A b w θ c k =
      psum c k / ((k : ℝ) - alpha θ) := by
  have hQ := Q5c_pos c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 k hk1 hkI
  have hW := Q5c_W c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 k hk1 hkI
  rw [← Bform_S γ A b w θ _ hb hAw hQ]
  set Q := Q5c γ A b w θ c k
  set X := ((A - b * w) / 3) ^ (3 / 2 : ℝ) * Q ^ (3 * θ / 2) with hX
  have hS : 0 < psum c k := psum_pos c hc0 k hk1 hkI
  have hk : (0:ℝ) < k := by exact_mod_cast hk1
  have hE : 0 < Q ^ (3 * θ / 2) := Real.rpow_pos_of_pos hQ _
  have ha : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hXp : 0 < X := by positivity
  clear_value X Q
  have h2 : 0 < 2 * (k:ℝ) - (2 - 3 * θ) := by
    have : (1:ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  have hXQ : X = Q * (b * psum c k / (γ * (2 * k - (2 - 3 * θ)))) := by
    field_simp at hW
    rw [← mul_div_assoc, eq_div_iff (by positivity)]
    linear_combination (-1) * hW
  have hα : (k : ℝ) - alpha θ = (2 * k - (2 - 3 * θ)) / 2 := by unfold alpha; ring
  rw [hα, hXQ]
  field_simp

theorem solution (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1) (j : Fin I) :
    c j ≤ γ * S A b w θ (Q5c γ A b w θ c ((j : ℕ) + 1)) / Q5c γ A b w θ c ((j : ℕ) + 1) ↔
      c j ≤ (psum c ((j : ℕ) + 1) / ((j : ℕ) + 1 : ℝ)) * ((j : ℕ) + 1 : ℝ) /
        (((j : ℕ) + 1 : ℝ) - alpha θ) := by
  have h := ratio_Q5c c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 ((j : ℕ) + 1) (by omega) (by omega)
  rw [h]
  have hk : (0:ℝ) < ((j : ℕ) + 1 : ℝ) := by positivity
  rw [div_mul_cancel₀ _ hk.ne']
  push_cast
  rfl
