-- Prove2me | solution 1 for CoProdBundle.Equil.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:17:09.514624+00:00
-- url     : https://prove2.me/submissions/249ed773-1d22-4439-af53-8c2e9f10871d

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

lemma psum_zero {I : ℕ} (c : Fin I → ℝ) : psum c 0 = 0 := by
  simp [psum]

lemma psum_succ {I : ℕ} (c : Fin I → ℝ) (k : ℕ) (h : k < I) :
    psum c (k+1) = psum c k + c ⟨k, h⟩ := by
  unfold psum
  have : Finset.univ.filter (fun j : Fin I => (j:ℕ) < k+1) =
      insert ⟨k,h⟩ (Finset.univ.filter (fun j : Fin I => (j:ℕ) < k)) := by
    ext j; simp [Fin.ext_iff]; omega
  rw [this, Finset.sum_insert (by simp)]
  ring

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

lemma Z_Q5c {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ : ℝ) (hb : 0 < b)
    (hAw : 0 < A - b * w) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (k : ℕ) (hk1 : 1 ≤ k)
    (hkI : k ≤ I) :
    b * Q5c γ A b w θ c k / (γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) *
      (Q5c γ A b w θ c k) ^ (3 * θ / 2))) = 2 * ((k : ℝ) - alpha θ) / psum c k := by
  have hW := Q5c_W c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 k hk1 hkI
  have hQ := Q5c_pos c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 k hk1 hkI
  have hS : 0 < psum c k := psum_pos c hc0 k hk1 hkI
  have hk : (0:ℝ) < k := by exact_mod_cast hk1
  have hE : 0 < (Q5c γ A b w θ c k) ^ (3 * θ / 2) := Real.rpow_pos_of_pos hQ _
  have ha : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have : b * Q5c γ A b w θ c k / (γ * (((A - b * w) / 3) ^ (3 / 2 : ℝ) *
      (Q5c γ A b w θ c k) ^ (3 * θ / 2))) =
      b / γ * (Q5c γ A b w θ c k / (((A - b * w) / 3) ^ (3 / 2 : ℝ) *
      (Q5c γ A b w θ c k) ^ (3 * θ / 2))) := by
    field_simp
  rw [this, hW]
  unfold alpha
  field_simp

lemma feasible_one {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) : Feasible c θ 1 := by
  refine ⟨le_refl _, by simpa using hI, ?_⟩
  have h1 : psum c 1 = c ⟨0, hI⟩ := by
    rw [psum_succ c 0 hI, psum_zero]; simp
  show c ⟨0, hI⟩ ≤ psum c 1 / (((1:ℕ):ℝ) - alpha θ)
  rw [h1]
  have : (((1:ℕ):ℝ) - alpha θ) = 3 * θ / 2 := by unfold alpha; push_cast; ring
  rw [this, le_div_iff₀ (by positivity)]
  nlinarith [hc0 ⟨0, hI⟩]

open Classical in
lemma Kstar_bounds {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) : 1 ≤ Kstar c θ ∧ Kstar c θ ≤ I := by
  refine ⟨?_, Nat.findGreatest_le I⟩
  exact Nat.le_findGreatest hI (feasible_one hI c hc0 θ hθ0 hθ1)


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

lemma ir_core (γ A b w θ : ℝ) {I : ℕ} (c : Fin I → ℝ) (hb : 0 < b) (hAw : 0 < A - b * w)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ)
    (q : Fin I → ℝ) (hq : IsNashEq γ A b w θ c q) (hQ : 0 < total q) (i : Fin I) :
    0 < q i ↔ c i < γ * S A b w θ (total q) / total q := by
  obtain ⟨hq0, hnash⟩ := hq
  have hR := R_nonneg q hq0 i
  have hQR : total q = q i + (total q - q i) := by ring
  have hκ : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hK0 : 0 < 2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ) := by positivity
  have hE : 0 < (total q) ^ (3 * θ / 2) := Real.rpow_pos_of_pos hQ _
  have hSQ : γ * S A b w θ (total q) / total q =
      (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (total q) ^ (3 * θ / 2) / total q := by
    rw [S_fac0 A b w θ _ hb hAw hQ.le]; ring
  rw [hSQ]
  constructor
  · intro hx
    have hmax : ∀ y : ℝ, 0 ≤ y →
        (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (y / (y + (total q - q i))) *
          (y + (total q - q i)) ^ (3 * θ / 2) - c i * y ≤
        (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (q i / (q i + (total q - q i))) *
          (q i + (total q - q i)) ^ (3 * θ / 2) - c i * q i := by
      intro y hy
      have : payoff γ A b w θ c (Function.update q i y) i ≤ payoff γ A b w θ c q i := hnash i y hy
      have e : payoff γ A b w θ c q i = payoff γ A b w θ c (Function.update q i (q i)) i := by
        rw [Function.update_eq_self]
      rw [e] at this
      rwa [payoff_form γ A b w θ c q i y hb hAw hy hR,
        payoff_form γ A b w θ c q i (q i) hb hAw hx.le hR] at this
    have hfoc := necessity (3 * θ / 2) _ (q i) _ (c i) hR hx hmax
    rw [← hQR] at hfoc
    rw [hfoc, div_lt_div_iff₀ (by positivity) hQ]
    have hβ : 3 * θ / 2 < 1 := by linarith
    have h1 : (total q - q i) + 3 * θ / 2 * q i < total q := by nlinarith
    have h2 : 0 < (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (total q) ^ (3 * θ / 2) := by
      positivity
    nlinarith [mul_pos h2 hQ]
  · intro hlt
    by_contra hnot
    have h0 : q i = 0 := le_antisymm (not_lt.mp hnot) (hq0 i)
    have hRQ : total q - q i = total q := by rw [h0]; ring
    have hc : c i < (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) *
        (total q - q i) ^ (3 * θ / 2) / (total q - q i) := by rw [hRQ]; exact hlt
    obtain ⟨y, hy0, hy⟩ := zero_best (3 * θ / 2) (total q - q i) _ (c i) (by rw [hRQ]; exact hQ) hc
    have h : payoff γ A b w θ c (Function.update q i y) i ≤ payoff γ A b w θ c q i :=
      hnash i y hy0.le
    have e : payoff γ A b w θ c q i = payoff γ A b w θ c (Function.update q i 0) i := by
      rw [← h0, Function.update_eq_self]
    rw [e, payoff_form γ A b w θ c q i y hb hAw hy0.le hR,
      payoff_form γ A b w θ c q i 0 hb hAw le_rfl hR] at h
    simp at h
    linarith
lemma pstar_optimal (γ A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hγ1 : γ < 1)
    (hQ : 0 ≤ Q) : IsRetailerOptimal γ A b w θ Q (Pstar A b w θ Q) := by
  intro P'
  unfold retailerProfit
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  rw [surplus_Pstar A b w θ Q hb hAw hQ]
  exact surplus_le A b w θ Q hb hAw hQ P'

lemma retailer_unique (γ A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hγ1 : γ < 1)
    (hQ : 0 < Q) (P : ℝ) (hP : IsRetailerOptimal γ A b w θ Q P) : P = Pstar A b w θ Q := by
  have h := hP (Pstar A b w θ Q)
  unfold retailerProfit at h
  have h2 : surplus A b w θ Q (Pstar A b w θ Q) ≤ surplus A b w θ Q P :=
    le_of_mul_le_mul_left h (by linarith)
  apply Pstar_unique A b w θ Q hb hAw hQ
  apply le_antisymm (surplus_le A b w θ Q hb hAw hQ.le P)
  rw [← surplus_Pstar A b w θ Q hb hAw hQ.le]
  exact h2

noncomputable def Cth {I : ℕ} (c : Fin I → ℝ) (θ : ℝ) (k : ℕ) : ℝ :=
  psum c k / ((k : ℝ) - alpha θ)

lemma feasible_step {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (k : ℕ) (hk : 2 ≤ k)
    (hf : Feasible c θ k) : Feasible c θ (k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  obtain ⟨_, h, hle⟩ := hf
  have hn1 : n + 1 < I := by simpa using h
  have hn : n < I := by omega
  have hps : psum c (n+2) = psum c (n+1) + c ⟨n+1, hn1⟩ := psum_succ c (n+1) hn1
  have hps1 : psum c (n+1) = psum c n + c ⟨n, hn⟩ := psum_succ c n hn
  refine ⟨by omega, by simpa using hn, ?_⟩
  have hmono : c ⟨n, hn⟩ ≤ c ⟨n+1, hn1⟩ := hcm (by simp [Fin.le_def])
  have hle' : c ⟨n+1, hn1⟩ ≤ psum c (n+2) / (((n+2:ℕ):ℝ) - alpha θ) := hle
  show c ⟨n, hn⟩ ≤ psum c (n+1) / (((n+1:ℕ):ℝ) - alpha θ)
  have hα : alpha θ < 1 := by unfold alpha; linarith
  have hd : (0:ℝ) < ((n+2:ℕ):ℝ) - alpha θ := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hd1 : (0:ℝ) < ((n+1:ℕ):ℝ) - alpha θ := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  rw [le_div_iff₀ hd] at hle'
  rw [le_div_iff₀ hd1]
  rw [hps] at hle'
  push_cast at hle' hd hd1 ⊢
  have := hc0 ⟨n+1, hn1⟩
  nlinarith [mul_le_mul_of_nonneg_right hmono hd1.le]

lemma feas_down {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    ∀ k : ℕ, Feasible c θ k → ∀ j : ℕ, 1 ≤ j → j ≤ k → Feasible c θ j := by
  intro k
  induction k with
  | zero => intro _ j hj hjk; omega
  | succ k ih =>
    intro hf j hj hjk
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · rw [h]; exact hf
    · have hk : 1 ≤ k := by omega
      have hf' : Feasible c θ k := by
        have := feasible_step c hc0 hcm θ hθ0 hθ1 (k + 1) (by omega) hf
        simpa using this
      exact ih hf' j hj (by omega)

lemma feas_iff_succ {I : ℕ} (c : Fin I → ℝ) (θ : ℝ) (j : ℕ) (hj : j < I) :
    Feasible c θ (j + 1) ↔ c ⟨j, hj⟩ ≤ Cth c θ (j + 1) := by
  unfold Feasible Cth
  constructor
  · rintro ⟨_, h, hle⟩
    exact hle
  · intro h
    exact ⟨by omega, hj, h⟩

lemma feas_next {I : ℕ} (c : Fin I → ℝ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j < I) :
    Feasible c θ (j + 1) ↔ c ⟨j, hj⟩ ≤ Cth c θ j := by
  rw [feas_iff_succ c θ j hj]
  unfold Cth
  have hα : alpha θ < 1 := by unfold alpha; linarith [hθ0]
  have hjr : (1:ℝ) ≤ j := by exact_mod_cast hj1
  have hd : (0:ℝ) < (j:ℝ) - alpha θ := by linarith
  have hd1 : (0:ℝ) < ((j + 1 : ℕ):ℝ) - alpha θ := by push_cast; linarith
  rw [psum_succ c j hj, le_div_iff₀ hd1, le_div_iff₀ hd]
  push_cast
  constructor <;> intro h <;> nlinarith [h]

lemma Cth_succ_eq {I : ℕ} (c : Fin I → ℝ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j < I) (h : c ⟨j, hj⟩ = Cth c θ j) : Cth c θ (j + 1) = Cth c θ j := by
  have hα : alpha θ < 1 := by unfold alpha; linarith [hθ0]
  have hjr : (1:ℝ) ≤ j := by exact_mod_cast hj1
  have hd : (0:ℝ) < (j:ℝ) - alpha θ := by linarith
  have hd1 : (0:ℝ) < ((j + 1 : ℕ):ℝ) - alpha θ := by push_cast; linarith
  unfold Cth at h ⊢
  rw [psum_succ c j hj, h]
  push_cast
  have hne1 : (j:ℝ) - alpha θ ≠ 0 := hd.ne'
  have hne2 : (j:ℝ) + 1 - alpha θ ≠ 0 := by linarith
  have hne3 : 1 + (j:ℝ) - alpha θ ≠ 0 := by linarith
  field_simp
  ring
open Classical in
lemma Kstar_spec {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) : Feasible c θ (Kstar c θ) :=
  Nat.findGreatest_spec (P := Feasible c θ) (m := 1) hI (feasible_one hI c hc0 θ hθ0 hθ1)

open Classical in
lemma Kstar_max {I : ℕ} (c : Fin I → ℝ) (θ : ℝ) (k : ℕ) (hk : Kstar c θ < k) (hkI : k ≤ I) :
    ¬ Feasible c θ k :=
  Nat.findGreatest_is_greatest hk hkI

open Classical in
lemma le_Kstar {I : ℕ} (c : Fin I → ℝ) (θ : ℝ) (k : ℕ) (hkI : k ≤ I) (hf : Feasible c θ k) :
    k ≤ Kstar c θ :=
  Nat.le_findGreatest hkI hf

lemma Cth_pos {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (θ : ℝ) (hθ0 : 0 < θ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkI : k ≤ I) : 0 < Cth c θ k := by
  unfold Cth
  have hS := psum_pos c hc0 k hk1 hkI
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have : (0:ℝ) < (k:ℝ) - alpha θ := by unfold alpha; linarith
  positivity

lemma c_le_C_of_feas {I : ℕ} (c : Fin I → ℝ) (hcm : Monotone c) (θ : ℝ) (k : ℕ)
    (hf : Feasible c θ k) (i : Fin I) (hi : (i : ℕ) < k) : c i ≤ Cth c θ k := by
  obtain ⟨_, h, hle⟩ := hf
  refine le_trans (hcm ?_) hle
  rw [Fin.le_def]
  show (i : ℕ) ≤ k - 1
  omega

lemma C_lt_c_of_ge {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (i : Fin I)
    (hi : Kstar c θ ≤ (i : ℕ)) : Cth c θ (Kstar c θ) < c i := by
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  have hKi : Kstar c θ < I := lt_of_le_of_lt hi i.2
  have hmax := Kstar_max c θ (Kstar c θ + 1) (by omega) (by omega)
  rw [feas_next c θ hθ0 hθ1 _ hK1 hKi] at hmax
  push_neg at hmax
  exact lt_of_lt_of_le hmax (hcm (by rw [Fin.le_def]; exact hi))

lemma Qstar_eq_Q5c {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ : ℝ)
    (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) :
    Qstar γ A b w θ c = Q5c γ A b w θ c (Kstar c θ) := by
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  set K := Kstar c θ with hK
  have hS : 0 < psum c K := psum_pos c hc0 K hK1 hKI
  have hk : (0:ℝ) < K := by exact_mod_cast hK1
  unfold Qstar Q5c
  have : (2 * γ / b) * (((K : ℝ) - alpha θ) / psum c K) =
      (γ / (b * (psum c K / K))) * (2 - (2 - 3 * θ) / K) := by
    unfold alpha
    field_simp
  rw [this]

lemma br_qstar {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ : ℝ)
    (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ)
    (i : Fin I) (hi : (i : ℕ) < Kstar c θ) :
    br4c γ A b w θ (c i) (Qstar γ A b w θ c) = qstar γ A b w θ c i := by
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  have hQeq := Qstar_eq_Q5c hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0
  set K := Kstar c θ with hK
  rw [hQeq]
  have hQ := Q5c_pos c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 K hK1 hKI
  rw [br_eq γ A b w θ (c i) _ hAw hQ, Z_Q5c c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 K hK1 hKI]
  unfold qstar
  rw [if_pos hi, ← hK, ← hQeq]
  have h23 : (2 - 3 * θ) ≠ 0 := ne_of_gt (by linarith)
  field_simp

lemma Qstar_pos {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ : ℝ)
    (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) :
    0 < Qstar γ A b w θ c := by
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  rw [Qstar_eq_Q5c hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0]
  exact Q5c_pos c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 _ hK1 hKI

lemma qstar_form {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (i : Fin I) (hi : (i : ℕ) < Kstar c θ) :
    qstar γ A b w θ c i =
      (1 - c i / Cth c θ (Kstar c θ)) * (2 * Qstar γ A b w θ c / (2 - 3 * θ)) := by
  unfold qstar Cth
  rw [if_pos hi, div_div_eq_mul_div]
  ring

lemma qstar_nonneg {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (γ A b w θ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (i : Fin I) : 0 ≤ qstar γ A b w θ c i := by
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  by_cases hi : (i : ℕ) < Kstar c θ
  · rw [qstar_form hI c hc0 γ A b w θ hθ0 hθ1 i hi]
    have hC := Cth_pos c hc0 θ hθ0 _ hK1 hKI
    have hle := c_le_C_of_feas c hcm θ _ (Kstar_spec hI c hc0 θ hθ0 hθ1) i hi
    have hQ := Qstar_pos hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0
    have h1 : c i / Cth c θ (Kstar c θ) ≤ 1 := (div_le_one hC).mpr hle
    have h23 : 0 < 2 - 3 * θ := by linarith
    apply mul_nonneg (by linarith) (by positivity)
  · unfold qstar; rw [if_neg hi]

lemma qstar_pos_iff {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (γ A b w θ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (i : Fin I) :
    0 < qstar γ A b w θ c i ↔
      ((i : ℕ) < Kstar c θ ∧ c i < psum c (Kstar c θ) / ((Kstar c θ : ℝ) - alpha θ)) := by
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  by_cases hi : (i : ℕ) < Kstar c θ
  · rw [qstar_form hI c hc0 γ A b w θ hθ0 hθ1 i hi]
    have hC := Cth_pos c hc0 θ hθ0 _ hK1 hKI
    have hQ := Qstar_pos hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0
    have h23 : 0 < 2 - 3 * θ := by linarith
    have hT : 0 < 2 * Qstar γ A b w θ c / (2 - 3 * θ) := by positivity
    rw [mul_pos_iff_of_pos_right hT, sub_pos, div_lt_one hC]
    exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
  · unfold qstar; rw [if_neg hi]
    simp [hi]

lemma total_qstar {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (γ A b w θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    total (qstar γ A b w θ c) = Qstar γ A b w θ c := by
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  have hS := psum_pos c hc0 _ hK1 hKI
  have hk : (0:ℝ) < (Kstar c θ : ℝ) := by exact_mod_cast hK1
  have h23 : (2 - 3 * θ) ≠ 0 := ne_of_gt (by linarith)
  unfold total
  have : ∑ j, qstar γ A b w θ c j = ∑ j ∈ Finset.univ.filter
      (fun j : Fin I => (j : ℕ) < Kstar c θ),
      (1 - c j * (((Kstar c θ : ℝ) - alpha θ) / psum c (Kstar c θ))) *
        (2 * Qstar γ A b w θ c / (2 - 3 * θ)) := by
    rw [Finset.sum_filter]; rfl
  rw [this, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const,
    card_lt _ hKI, nsmul_eq_mul]
  have e : (Finset.univ.filter (fun j : Fin I => (j : ℕ) < Kstar c θ)).sum (fun j => c j) =
      psum c (Kstar c θ) := rfl
  rw [e]
  have e2 : ((Kstar c θ : ℝ) * 1 - psum c (Kstar c θ) *
      (((Kstar c θ : ℝ) - alpha θ) / psum c (Kstar c θ))) = alpha θ := by
    field_simp; ring
  rw [e2]
  unfold alpha
  field_simp

lemma qstar_K1 {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (γ A b w θ : ℝ) (hb : 0 < b) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hK : Kstar c θ = 1) :
    qstar γ A b w θ c ⟨0, hI⟩ =
      (3 * γ * θ / (b * c ⟨0, hI⟩)) ^ (2 / (2 - 3 * θ)) * ((A - b * w) / 3) ^ (3 / (2 - 3 * θ)) := by
  have hps : psum c 1 = c ⟨0, hI⟩ := by
    rw [psum_succ c 0 hI, psum_zero]; simp
  have h23 : (2 - 3 * θ) ≠ 0 := ne_of_gt (by linarith)
  have hc := hc0 ⟨0, hI⟩
  unfold qstar Qstar
  rw [hK]
  simp only [Nat.cast_one]
  rw [if_pos (by simp), hps]
  have e1 : (1 - c ⟨0, hI⟩ * ((1 - alpha θ) / c ⟨0, hI⟩)) = 1 - 3 * θ / 2 := by
    unfold alpha; field_simp; ring
  have e2 : (2 * γ / b) * ((1 - alpha θ) / c ⟨0, hI⟩) = 3 * γ * θ / (b * c ⟨0, hI⟩) := by
    unfold alpha; field_simp; ring
  rw [e1, e2]
  set X := (3 * γ * θ / (b * c ⟨0, hI⟩)) ^ (2 / (2 - 3 * θ)) * ((A - b * w) / 3) ^ (3 / (2 - 3 * θ))
  field_simp
lemma gS_eq (γ A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 < Q) :
    γ * S A b w θ Q / Q =
      (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * Q ^ (3 * θ / 2) / Q := by
  rw [S_fac0 A b w θ _ hb hAw hQ.le]; ring

lemma no_entry (β R K0 c : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R) (hK0 : 0 < K0)
    (hc : K0 * R ^ β / R ≤ c) (y : ℝ) (hy : 0 ≤ y) :
    K0 * (y / (y + R)) * (y + R) ^ β - c * y ≤ 0 := by
  have hY : 0 < y + R := by linarith
  have hb := bern_bound (y + R) R β hY hR hβ0.le hβ1.le
  have hp : 0 < R ^ β := Real.rpow_pos_of_pos hR β
  have h1 : (y + R) ^ β ≤ R ^ β * (y + R) / R := by
    have : R ^ β * (1 + β * ((y + R) / R - 1)) ≤ R ^ β * (y + R) / R := by
      have e : R ^ β * (y + R) / R = R ^ β * (1 + y / R) := by field_simp; ring
      have e2 : (y + R) / R - 1 = y / R := by field_simp; ring
      rw [e, e2]
      apply mul_le_mul_of_nonneg_left _ hp.le
      have : 0 ≤ y / R := by positivity
      nlinarith
    linarith
  have h2 : K0 * (y / (y + R)) * (y + R) ^ β ≤ y * (K0 * R ^ β / R) := by
    calc K0 * (y / (y + R)) * (y + R) ^ β ≤ K0 * (y / (y + R)) * (R ^ β * (y + R) / R) := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
      _ = y * (K0 * R ^ β / R) := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hc hy]

lemma zero_profile_dev (β K0 c : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hc : 0 < c) :
    ∃ y : ℝ, 0 < y ∧ 0 < K0 * (y / (y + 0)) * (y + 0) ^ β - c * y := by
  set t := K0 / (2 * c) with ht
  have htp : 0 < t := by positivity
  have hα : 0 < 1 - β := by linarith
  set y := t ^ ((1 - β)⁻¹) with hy
  have hyp : 0 < y := Real.rpow_pos_of_pos htp _
  have hyt : y ^ (1 - β) = t := Real.rpow_inv_rpow htp.le hα.ne'
  have hprod : y ^ β * y ^ (1 - β) = y := by
    rw [← Real.rpow_add hyp]; simp
  refine ⟨y, hyp, ?_⟩
  rw [add_zero, div_self hyp.ne', mul_one]
  have : y ^ β * t = y := by rw [← hyt]; exact hprod
  have h3 : y ^ β = y / t := by field_simp; linarith
  rw [h3, ht]
  field_simp
  nlinarith [mul_pos hc hyp]
lemma B_Qstar {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (γ A b w θ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) :
    (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (Qstar γ A b w θ c) ^ (3 * θ / 2) /
      Qstar γ A b w θ c = Cth c θ (Kstar c θ) := by
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  have hQeq := Qstar_eq_Q5c hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0
  have hQ := Qstar_pos hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0
  rw [← gS_eq γ A b w θ _ hb hAw hQ, hQeq]
  exact ratio_Q5c c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 _ hK1 hKI

lemma nash_qstar {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (γ A b w θ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) :
    IsNashEq γ A b w θ c (qstar γ A b w θ c) := by
  have hq0 := qstar_nonneg hI c hc0 hcm γ A b w θ hb hAw hθ0 hθ1 hγ0
  refine ⟨hq0, fun i x hx => ?_⟩
  show payoff γ A b w θ c (Function.update (qstar γ A b w θ c) i x) i ≤
    payoff γ A b w θ c (qstar γ A b w θ c) i
  set qs := qstar γ A b w θ c with hqs
  have hR := R_nonneg qs hq0 i
  have htot : total qs = Qstar γ A b w θ c := total_qstar hI c hc0 γ A b w θ hθ0 hθ1
  have hQ := Qstar_pos hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0
  have e : payoff γ A b w θ c qs i = payoff γ A b w θ c (Function.update qs i (qs i)) i := by
    rw [Function.update_eq_self]
  rw [e, payoff_form γ A b w θ c qs i x hb hAw hx hR,
    payoff_form γ A b w θ c qs i (qs i) hb hAw (hq0 i) hR]
  have hK0 : 0 < 2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ) := by
    have : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  by_cases hpos : 0 < qs i
  · have hfoc : qs i = br4c γ A b w θ (c i) (qs i + (total qs - qs i)) := by
      have : qs i + (total qs - qs i) = Qstar γ A b w θ c := by rw [← htot]; ring
      rw [this]
      have hi := ((qstar_pos_iff hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 i).mp hpos).1
      exact (br_qstar hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 i hi).symm
    exact sufficiency (3 * θ / 2) _ (qs i) x _ (c i) (by linarith) (by linarith) hR hpos hx hK0
      ((foc_iff γ A b w θ (c i) _ (qs i) hb hAw hθ0 hθ1 hγ0 hR hpos).mpr hfoc)
  · have h0 : qs i = 0 := le_antisymm (not_lt.mp hpos) (hq0 i)
    have hRQ : total qs - qs i = Qstar γ A b w θ c := by rw [h0, htot]; ring
    have hcC : Cth c θ (Kstar c θ) ≤ c i := by
      by_cases hi : (i : ℕ) < Kstar c θ
      · have := (qstar_pos_iff hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 i).not.mp hpos
        have h2 : ¬ c i < psum c (Kstar c θ) / ((Kstar c θ : ℝ) - alpha θ) := fun h => this ⟨hi, h⟩
        exact not_lt.mp h2
      · exact (C_lt_c_of_ge hI c hc0 hcm θ hθ0 hθ1 i (not_lt.mp hi)).le
    have := no_entry (3 * θ / 2) (total qs - qs i) _ (c i) (by linarith) (by linarith)
      (by rw [hRQ]; exact hQ) hK0
      (by rw [hRQ, B_Qstar hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0]; exact hcC) x hx
    rw [h0] at this ⊢
    simpa using this
lemma nash_foc (γ A b w θ : ℝ) {I : ℕ} (c : Fin I → ℝ) (hb : 0 < b) (hAw : 0 < A - b * w)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ)
    (q : Fin I → ℝ) (hq : IsNashEq γ A b w θ c q) (i : Fin I) (hx : 0 < q i) :
    q i = br4c γ A b w θ (c i) (total q) := by
  obtain ⟨hq0, hnash⟩ := hq
  have hR := R_nonneg q hq0 i
  have hmax : ∀ y : ℝ, 0 ≤ y →
      (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (y / (y + (total q - q i))) *
        (y + (total q - q i)) ^ (3 * θ / 2) - c i * y ≤
      (2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) * (q i / (q i + (total q - q i))) *
        (q i + (total q - q i)) ^ (3 * θ / 2) - c i * q i := by
    intro y hy
    have : payoff γ A b w θ c (Function.update q i y) i ≤ payoff γ A b w θ c q i := hnash i y hy
    have e : payoff γ A b w θ c q i = payoff γ A b w θ c (Function.update q i (q i)) i := by
      rw [Function.update_eq_self]
    rw [e] at this
    rwa [payoff_form γ A b w θ c q i y hb hAw hy hR,
      payoff_form γ A b w θ c q i (q i) hb hAw hx.le hR] at this
  have hfoc := (foc_iff γ A b w θ (c i) _ (q i) hb hAw hθ0 hθ1 hγ0 hR hx).mp
    (necessity (3 * θ / 2) _ (q i) _ (c i) hR hx hmax)
  have : q i + (total q - q i) = total q := by ring
  rwa [this] at hfoc

lemma nash_total_pos (γ A b w θ : ℝ) {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ)
    (q : Fin I → ℝ) (hq : IsNashEq γ A b w θ c q) : 0 < total q := by
  by_contra hneg
  obtain ⟨hq0, hnash⟩ := hq
  have hsum : 0 ≤ total q := Finset.sum_nonneg (fun j _ => hq0 j)
  have h0 : total q = 0 := le_antisymm (not_lt.mp hneg) hsum
  set i0 : Fin I := ⟨0, hI⟩ with hi0
  have hqi : q i0 = 0 := by
    have : q i0 ≤ total q := Finset.single_le_sum (fun j _ => hq0 j) (Finset.mem_univ i0)
    exact le_antisymm (by linarith) (hq0 i0)
  have hR : total q - q i0 = 0 := by rw [h0, hqi]; ring
  have hR' : 0 ≤ total q - q i0 := by rw [hR]
  have hK0 : 0 < 2 * γ / b * ((A - b * w) / 3) ^ (3 / 2 : ℝ) := by
    have : 0 < ((A - b * w) / 3) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  obtain ⟨y, hy0, hy⟩ := zero_profile_dev (3 * θ / 2) _ (c i0) (by linarith) (by linarith) hK0
    (hc0 i0)
  have h : payoff γ A b w θ c (Function.update q i0 y) i0 ≤ payoff γ A b w θ c q i0 :=
    hnash i0 y hy0.le
  have e : payoff γ A b w θ c q i0 = payoff γ A b w θ c (Function.update q i0 0) i0 := by
    rw [← hqi, Function.update_eq_self]
  rw [e, payoff_form γ A b w θ c q i0 y hb hAw hy0.le hR',
    payoff_form γ A b w θ c q i0 0 hb hAw le_rfl hR', hR] at h
  simp at h hy
  linarith
lemma Q5c_of_C {I : ℕ} (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i) (γ A b w θ : ℝ) (hb : 0 < b)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (k k' : ℕ) (hk1 : 1 ≤ k) (hkI : k ≤ I)
    (hk1' : 1 ≤ k') (hkI' : k' ≤ I) (h : Cth c θ k = Cth c θ k') :
    Q5c γ A b w θ c k = Q5c γ A b w θ c k' := by
  have base : ∀ k : ℕ, 1 ≤ k → k ≤ I →
      (γ / (b * (psum c k / k))) * (2 - (2 - 3 * θ) / k) = 2 * γ / (b * Cth c θ k) := by
    intro k hk1 hkI
    have hS := psum_pos c hc0 k hk1 hkI
    have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk1
    have hd : (0:ℝ) < (k:ℝ) - alpha θ := by unfold alpha; linarith
    unfold Cth
    unfold alpha at hd ⊢
    have hk0 : (k:ℝ) ≠ 0 := by positivity
    have hd' : (k:ℝ) - (1 - 3 * θ / 2) ≠ 0 := hd.ne'
    field_simp
  unfold Q5c
  rw [base k hk1 hkI, base k' hk1' hkI', h]

lemma nash_unique {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (γ A b w θ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (q : Fin I → ℝ) (hq : IsNashEq γ A b w θ c q) :
    q = qstar γ A b w θ c := by
  classical
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  have hq0 := hq.1
  have hQ := nash_total_pos γ A b w θ hI c hc0 hb hAw hθ0 hθ1 hγ0 q hq
  have hir := fun i => ir_core γ A b w θ c hb hAw hθ0 hθ1 hγ0 q hq hQ i
  have hpre : ∀ i j : Fin I, i ≤ j → 0 < q j → 0 < q i :=
    fun i j hij hj => (hir i).mpr (lt_of_le_of_lt (hcm hij) ((hir j).mp hj))
  obtain ⟨m, hmI, hPm, hm3⟩ : ∃ m : ℕ, m ≤ I ∧ (∀ i : Fin I, (i : ℕ) < m → 0 < q i) ∧
      ∀ i : Fin I, m ≤ (i : ℕ) → q i = 0 := by
    set P : ℕ → Prop := fun k => ∀ i : Fin I, (i : ℕ) < k → 0 < q i with hP
    refine ⟨Nat.findGreatest P I, Nat.findGreatest_le I, ?_, ?_⟩
    · exact Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le I)
        (fun i hi => absurd hi (Nat.not_lt_zero _))
    · intro i hi
      by_contra hne
      have hpos : 0 < q i := lt_of_le_of_ne (hq0 i) (Ne.symm hne)
      have hP1 : P ((i : ℕ) + 1) := fun i' hi' => hpre i' i (by rw [Fin.le_def]; omega) hpos
      have := Nat.le_findGreatest (P := P) (by have := i.2; omega : (i : ℕ) + 1 ≤ I) hP1
      omega
  have hm1 : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have : total q = 0 := Finset.sum_eq_zero (fun i _ => hm3 i (by omega))
    linarith
  have hsumq : ∑ i ∈ Finset.univ.filter (fun i : Fin I => (i : ℕ) < m),
      br4c γ A b w θ (c i) (total q) = total q := by
    have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin I => (i : ℕ) < m),
        br4c γ A b w θ (c i) (total q) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin I => (i : ℕ) < m), q i :=
      Finset.sum_congr rfl (fun i hi =>
        (nash_foc γ A b w θ c hb hAw hθ0 hθ1 hγ0 q hq i (hPm i (by simpa using hi))).symm)
    rw [h1]
    unfold total
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun i _ => by
      split_ifs with h
      · rfl
      · exact (hm3 i (not_lt.mp h)).symm)
  have hW := (five_b_iff c hc0 γ A b w θ (total q) hb hAw hθ0 hθ1 hγ0 m hm1 hmI hQ).mp hsumq.symm
  have hQ5 : total q = Q5c γ A b w θ c m :=
    (Q_iff ((A - b * w) / 3) _ θ (total q) (by positivity)
      (M_pos c hc0 γ b θ hb hθ0 hθ1 hγ0 m hm1 hmI) hθ0 hθ1 hQ).mp hW
  have hB : γ * S A b w θ (total q) / total q = Cth c θ m := by
    rw [hQ5]; exact ratio_Q5c c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 m hm1 hmI
  have hact : ∀ i : Fin I, (i : ℕ) < m → c i < Cth c θ m := fun i hi => by
    rw [← hB]; exact (hir i).mp (hPm i hi)
  have hinact : ∀ i : Fin I, m ≤ (i : ℕ) → Cth c θ m ≤ c i := fun i hi => by
    rw [← hB]
    by_contra h
    have := (hir i).mpr (not_le.mp h)
    rw [hm3 i hi] at this
    exact lt_irrefl _ this
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hfeas_m : Feasible c θ m := by
    subst hm'
    rw [feas_iff_succ c θ m' (by omega)]
    exact (hact ⟨m', by omega⟩ (by simp)).le
  have hKspec := Kstar_spec hI c hc0 θ hθ0 hθ1
  have hmK : m ≤ Kstar c θ := le_Kstar c θ m hmI hfeas_m
  have claim : ∀ j : ℕ, m ≤ j → j ≤ Kstar c θ → Cth c θ j = Cth c θ m := by
    intro j hmj
    induction j, hmj using Nat.le_induction with
    | base => intro _; rfl
    | succ j hmj ih =>
      intro hjK
      have hjI : j < I := by omega
      have hj1 : 1 ≤ j := by omega
      have ih' := ih (by omega)
      have h1 : c ⟨j, hjI⟩ ≤ Cth c θ j :=
        (feas_next c θ hθ0 hθ1 j hj1 hjI).mp
          (feas_down c hc0 hcm θ hθ0 hθ1 _ hKspec (j + 1) (by omega) hjK)
      have h2 : Cth c θ m ≤ c ⟨j, hjI⟩ := hinact ⟨j, hjI⟩ hmj
      have h3 : c ⟨j, hjI⟩ = Cth c θ j := le_antisymm h1 (by rw [ih']; exact h2)
      rw [Cth_succ_eq c θ hθ0 hθ1 j hj1 hjI h3, ih']
  have hcj : ∀ (j : ℕ) (hj : j < I), m ≤ j → j < Kstar c θ → c ⟨j, hj⟩ = Cth c θ m := by
    intro j hj hmj hjK
    have hj1 : 1 ≤ j := by omega
    have h1 : c ⟨j, hj⟩ ≤ Cth c θ j :=
      (feas_next c θ hθ0 hθ1 j hj1 hj).mp
        (feas_down c hc0 hcm θ hθ0 hθ1 _ hKspec (j + 1) (by omega) hjK)
    rw [claim j hmj hjK.le] at h1
    exact le_antisymm h1 (hinact ⟨j, hj⟩ hmj)
  have hCK : Cth c θ (Kstar c θ) = Cth c θ m := claim _ hmK le_rfl
  have hQeq : total q = Qstar γ A b w θ c := by
    rw [hQ5, Qstar_eq_Q5c hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0]
    exact Q5c_of_C c hc0 γ A b w θ hb hθ0 hθ1 m _ hm1 hmI hK1 hKI hCK.symm
  funext i
  by_cases him : (i : ℕ) < m
  · rw [nash_foc γ A b w θ c hb hAw hθ0 hθ1 hγ0 q hq i (hPm i him), hQeq]
    exact br_qstar hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0 i (by omega)
  · have hi0 : q i = 0 := hm3 i (not_lt.mp him)
    rw [hi0]
    by_cases hiK : (i : ℕ) < Kstar c θ
    · rw [qstar_form hI c hc0 γ A b w θ hθ0 hθ1 i hiK]
      have hci : c i = Cth c θ m := hcj i i.2 (not_lt.mp him) hiK
      have hCm := Cth_pos c hc0 θ hθ0 m hm1 hmI
      rw [hci, hCK, div_self hCm.ne']
      simp
    · unfold qstar; rw [if_neg hiK]
lemma K_one_iff {I : ℕ} (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) (h : 1 < I) :
    Kstar c θ = 1 ↔ 2 * c ⟨0, hI⟩ / (3 * θ) < c ⟨1, h⟩ := by
  obtain ⟨hK1, hKI⟩ := Kstar_bounds hI c hc0 θ hθ0 hθ1
  have hC1 : Cth c θ 1 = 2 * c ⟨0, hI⟩ / (3 * θ) := by
    unfold Cth
    have hps : psum c 1 = c ⟨0, hI⟩ := by
      rw [psum_succ c 0 hI, psum_zero]; simp
    rw [hps]
    unfold alpha
    push_cast
    field_simp
    ring
  have hf2 : Feasible c θ (1 + 1) ↔ c ⟨1, h⟩ ≤ Cth c θ 1 := feas_next c θ hθ0 hθ1 1 le_rfl h
  rw [← hC1]
  constructor
  · intro hK
    have := Kstar_max c θ (1 + 1) (by omega) (by omega)
    rw [hf2] at this
    exact not_le.mp this
  · intro hlt
    have hnot : ¬ Feasible c θ (1 + 1) := by rw [hf2]; exact not_le.mpr hlt
    by_contra hne
    have h2 : 2 ≤ Kstar c θ := by omega
    exact hnot (feas_down c hc0 hcm θ hθ0 hθ1 _ (Kstar_spec hI c hc0 θ hθ0 hθ1) 2 (by omega) h2)
theorem solution (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (1 ≤ Kstar c θ ∧ Kstar c θ ≤ I) ∧
    (∀ Q : ℝ, 0 < Q → IsRetailerOptimal γ A b w θ Q (Pstar A b w θ Q) ∧
      ∀ P : ℝ, IsRetailerOptimal γ A b w θ Q P → P = Pstar A b w θ Q) ∧
    (∀ q : Fin I → ℝ, IsNashEq γ A b w θ c q ↔ q = qstar γ A b w θ c) ∧
    total (qstar γ A b w θ c) = Qstar γ A b w θ c ∧
    (∀ i, 0 ≤ qstar γ A b w θ c i) ∧
    (∀ i, 0 < qstar γ A b w θ c i ↔
      ((i : ℕ) < Kstar c θ ∧ c i < psum c (Kstar c θ) / ((Kstar c θ : ℝ) - alpha θ))) ∧
    (Kstar c θ = 1 → qstar γ A b w θ c ⟨0, hI⟩ =
      (3 * γ * θ / (b * c ⟨0, hI⟩)) ^ (2 / (2 - 3 * θ)) * ((A - b * w) / 3) ^ (3 / (2 - 3 * θ))) ∧
    (∀ h : 1 < I, Kstar c θ = 1 ↔ 2 * c ⟨0, hI⟩ / (3 * θ) < c ⟨1, h⟩) := by
  refine ⟨Kstar_bounds hI c hc0 θ hθ0 hθ1, ?_, ?_, total_qstar hI c hc0 γ A b w θ hθ0 hθ1,
    qstar_nonneg hI c hc0 hcm γ A b w θ hb hAw hθ0 hθ1 hγ0,
    qstar_pos_iff hI c hc0 γ A b w θ hb hAw hθ0 hθ1 hγ0,
    fun hK => qstar_K1 hI c hc0 γ A b w θ hb hθ0 hθ1 hK,
    fun h => K_one_iff hI c hc0 hcm θ hθ0 hθ1 h⟩
  · exact fun Q hQ => ⟨pstar_optimal γ A b w θ Q hb hAw hγ1 hQ.le,
      fun P hP => retailer_unique γ A b w θ Q hb hAw hγ1 hQ P hP⟩
  · intro q
    constructor
    · exact nash_unique hI c hc0 hcm γ A b w θ hb hAw hθ0 hθ1 hγ0 q
    · rintro rfl
      exact nash_qstar hI c hc0 hcm γ A b w θ hb hAw hθ0 hθ1 hγ0
