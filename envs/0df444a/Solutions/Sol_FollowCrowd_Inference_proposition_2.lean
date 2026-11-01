-- Prove2me | solution 1 for FollowCrowd.Inference.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:02:04.590891+00:00
-- url     : https://prove2.me/submissions/fb606d06-234c-44eb-9aee-73b710b256ef

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model
import Theorems.Thm_FollowCrowd_Inference_lemma_1

namespace Aux_FCProp2
open FollowCrowd.Inference

/-! ### Basic facts on the law -/

lemma weight_nonneg (P : Params) {mu : ℝ} (hmu : 0 < mu) (hlam : 0 < P.lam) {p : ℕ → ℝ}
    (hp : IsJoinVec p) (n : ℕ) : 0 ≤ weight P mu p n :=
  mul_nonneg (pow_nonneg (div_pos hlam hmu).le _) (Finset.prod_nonneg fun i _ => (hp.2 i).1)

lemma weight_zero (P : Params) (mu : ℝ) (p : ℕ → ℝ) : weight P mu p 0 = 1 := by
  simp [weight]

/-- normalising constant -/
noncomputable def Z (P : Params) (mu : ℝ) (p : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (Nbar P + 1), weight P mu p j

lemma Z_pos (P : Params) {mu : ℝ} (hmu : 0 < mu) (hlam : 0 < P.lam) {p : ℕ → ℝ}
    (hp : IsJoinVec p) : 0 < Z P mu p := by
  have := Finset.single_le_sum (f := weight P mu p) (fun i _ => weight_nonneg P hmu hlam hp i)
    (Finset.mem_range.2 (Nat.succ_pos (Nbar P)))
  rw [weight_zero] at this
  unfold Z; linarith

lemma stat0 (P : Params) (mu : ℝ) (p : ℕ → ℝ) : stat P mu p 0 = 1 / Z P mu p := by
  rw [stat, if_pos (Nat.zero_le _), weight_zero]; rfl

lemma stat_nonneg (P : Params) {mu : ℝ} (hmu : 0 < mu) (hlam : 0 < P.lam) {p : ℕ → ℝ}
    (hp : IsJoinVec p) (n : ℕ) : 0 ≤ stat P mu p n := by
  unfold stat; split_ifs
  · exact div_nonneg (weight_nonneg P hmu hlam hp n) (Z_pos P hmu hlam hp).le
  · exact le_refl _

lemma theta_eq (P : Params) (p : ℕ → ℝ) (n : ℕ) :
    theta P p n = P.γ * (1 / Z P P.muH p) /
      (P.γ * (1 / Z P P.muH p) + (1 - P.γ) * (1 / Z P P.muL p) *
        (rho P P.muL / rho P P.muH) ^ n) := by
  rw [theta, stat0, stat0]

/-! ### The threshold profile -/

lemma thr_eq (v : ℝ) (hv : 0 ≤ v) (i : ℕ) :
    thrProfile v i = max 0 (min 1 (v - i + 1)) := by
  unfold thrProfile
  have h1 := Nat.floor_le hv
  have h2 := Nat.lt_floor_add_one v
  split_ifs with ha hb
  · have : (i : ℝ) ≤ ⌊v⌋₊ := by exact_mod_cast ha
    rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
  · subst hb
    push_cast
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · have : (⌊v⌋₊ : ℝ) + 2 ≤ i := by
      have : ⌊v⌋₊ + 2 ≤ i := by omega
      exact_mod_cast this
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]

lemma thr_join (v : ℝ) (hv : 0 ≤ v) : IsJoinVec (thrProfile v) := by
  refine ⟨?_, fun i => ?_⟩
  · simp [thrProfile]
  · rw [thr_eq v hv]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma thr_mono {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (i : ℕ) :
    thrProfile v i ≤ thrProfile w i := by
  rw [thr_eq v hv, thr_eq w (le_trans hv hvw)]
  exact max_le_max (le_refl _) (min_le_min (le_refl _) (by linarith))

lemma thr_cont (i : ℕ) : ContinuousOn (fun v => thrProfile v i) (Set.Ici 0) := by
  have : ContinuousOn (fun v : ℝ => max 0 (min 1 (v - i + 1))) (Set.Ici 0) := by
    fun_prop
  exact this.congr (fun v hv => thr_eq v hv i)

lemma thr_pos {v : ℝ} (hv : 0 ≤ v) {i : ℕ} (hi : (i : ℝ) < v + 1) : 0 < thrProfile v i := by
  rw [thr_eq v hv]
  exact lt_max_of_lt_right (lt_min one_pos (by linarith))

lemma thr_zero {v : ℝ} (hv : 0 ≤ v) {i : ℕ} (hi : v + 1 ≤ (i : ℝ)) : thrProfile v i = 0 := by
  rw [thr_eq v hv]
  exact max_eq_left (min_le_of_right_le (by linarith))

lemma thr_one {v : ℝ} (hv : 0 ≤ v) {i : ℕ} (hi : (i : ℝ) ≤ v) : thrProfile v i = 1 := by
  rw [thr_eq v hv, min_eq_left (by linarith), max_eq_right (by norm_num)]


/-! ### Product comparison -/

lemma prod_cross {p p' : ℕ → ℝ} (hp : IsJoinVec p) (hp' : IsJoinVec p')
    (hle : ∀ i, p i ≤ p' i) {j k : ℕ} (hjk : j ≤ k) :
    (∏ i ∈ Finset.range j, p' i) * (∏ i ∈ Finset.range k, p i) ≤
      (∏ i ∈ Finset.range j, p i) * (∏ i ∈ Finset.range k, p' i) := by
  rw [← Finset.prod_range_mul_prod_Ico p hjk, ← Finset.prod_range_mul_prod_Ico p' hjk]
  have h0 : 0 ≤ ∏ i ∈ Finset.range j, p i := Finset.prod_nonneg fun i _ => (hp.2 i).1
  have h0' : 0 ≤ ∏ i ∈ Finset.range j, p' i := Finset.prod_nonneg fun i _ => (hp'.2 i).1
  have hI : ∏ i ∈ Finset.Ico j k, p i ≤ ∏ i ∈ Finset.Ico j k, p' i :=
    Finset.prod_le_prod (fun i _ => (hp.2 i).1) (fun i _ => hle i)
  have := mul_le_mul_of_nonneg_left hI (mul_nonneg h0 h0')
  nlinarith

/-- Z_L(p) Z_H(p') ≤ Z_L(p') Z_H(p): the inference effect (weak form). -/
lemma Z_cross (P : Params) (hP : P.Standing) {p p' : ℕ → ℝ} (hp : IsJoinVec p)
    (hp' : IsJoinVec p') (hle : ∀ i, p i ≤ p' i) :
    Z P P.muL p * Z P P.muH p' ≤ Z P P.muL p' * Z P P.muH p := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  set a := rho P P.muL
  set b := rho P P.muH
  have hb : 0 < b := div_pos hlam hH
  have hab : b ≤ a := (div_lt_div_of_pos_left hlam hL hLH).le
  set c : ℕ → ℝ := fun j => ∏ i ∈ Finset.range j, p i
  set c' : ℕ → ℝ := fun j => ∏ i ∈ Finset.range j, p' i
  set S := Finset.range (Nbar P + 1)
  have eL : Z P P.muL p * Z P P.muH p' = ∑ j ∈ S, ∑ k ∈ S, a ^ j * b ^ k * (c j * c' k) := by
    unfold Z weight rho
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [a, b, c, c', rho]; ring
  have eR : Z P P.muL p' * Z P P.muH p = ∑ j ∈ S, ∑ k ∈ S, a ^ j * b ^ k * (c' j * c k) := by
    unfold Z weight rho
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [a, b, c, c', rho]; ring
  rw [eL, eR, ← sub_nonneg, ← Finset.sum_sub_distrib]
  set f : ℕ → ℕ → ℝ := fun j k => a ^ j * b ^ k * (c' j * c k) - a ^ j * b ^ k * (c j * c' k)
  have hsum : ∑ j ∈ S, ∑ k ∈ S, f j k = ∑ j ∈ S, ∑ k ∈ S, f k j := Finset.sum_comm
  have key : ∀ j k, 0 ≤ f j k + f k j := by
    have main : ∀ j k, j ≤ k → 0 ≤ f j k + f k j := by
      intro j k hjk
      have h1 := prod_cross hp hp' hle hjk
      have h2 : a ^ j * b ^ k ≤ a ^ k * b ^ j := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
        rw [pow_add, pow_add]
        have : b ^ d ≤ a ^ d := pow_le_pow_left₀ hb.le hab d
        have ha0 : 0 ≤ a ^ j := pow_nonneg (le_trans hb.le hab) j
        have hb0 : 0 ≤ b ^ j := pow_nonneg hb.le j
        calc a ^ j * (b ^ j * b ^ d) = (a ^ j * b ^ j) * b ^ d := by ring
          _ ≤ (a ^ j * b ^ j) * a ^ d := mul_le_mul_of_nonneg_left this (mul_nonneg ha0 hb0)
          _ = a ^ j * a ^ d * b ^ j := by ring
      have e : f j k + f k j = (a ^ k * b ^ j - a ^ j * b ^ k) * (c j * c' k - c' j * c k) := by
        simp only [f]; ring
      rw [e]
      exact mul_nonneg (by linarith) (by simp only [c, c'] at h1 ⊢; linarith)
    intro j k
    rcases le_total j k with h | h
    · exact main j k h
    · have := main k j h; linarith
  have : 2 * ∑ j ∈ S, ∑ k ∈ S, f j k = ∑ j ∈ S, ∑ k ∈ S, (f j k + f k j) := by
    rw [two_mul]
    conv_lhs => arg 2; rw [hsum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
  have h3 : 0 ≤ ∑ j ∈ S, ∑ k ∈ S, (f j k + f k j) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => key j k
  have h4 : 0 ≤ ∑ j ∈ S, ∑ k ∈ S, f j k := by linarith
  simpa [f] using h4


/-! ### Monotonicity of the belief and utility -/

lemma theta_eq' (P : Params) (hP : P.Standing) {p : ℕ → ℝ} (hp : IsJoinVec p) (n : ℕ) :
    theta P p n = P.γ * Z P P.muL p /
      (P.γ * Z P P.muL p + (1 - P.γ) * (rho P P.muL / rho P P.muH) ^ n * Z P P.muH p) := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  have h1 := Z_pos P hH hlam hp
  have h2 := Z_pos P hL hlam hp
  rw [theta_eq]
  field_simp

lemma rr_pos (P : Params) (hP : P.Standing) (n : ℕ) : 0 < (rho P P.muL / rho P P.muH) ^ n := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  exact pow_pos (div_pos (div_pos hlam hL) (div_pos hlam hH)) n

lemma theta_mono (P : Params) (hP : P.Standing) {p p' : ℕ → ℝ} (hp : IsJoinVec p)
    (hp' : IsJoinVec p') (hle : ∀ i, p i ≤ p' i) (n : ℕ) :
    theta P p n ≤ theta P p' n := by
  have hc := Z_cross P hP hp hp' hle
  have hr := rr_pos P hP n
  rw [theta_eq' P hP hp, theta_eq' P hP hp']
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  have a1 := Z_pos P hH hlam hp
  have a2 := Z_pos P hL hlam hp
  have a3 := Z_pos P hH hlam hp'
  have a4 := Z_pos P hL hlam hp'
  set K := (1 - P.γ) * (rho P P.muL / rho P P.muH) ^ n
  have hK : 0 < K := mul_pos (by linarith) hr
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : P.γ * K * (Z P P.muL p * Z P P.muH p') ≤ P.γ * K * (Z P P.muL p' * Z P P.muH p) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  nlinarith

lemma theta_mem (P : Params) (hP : P.Standing) {p : ℕ → ℝ} (hp : IsJoinVec p) (n : ℕ) :
    0 ≤ theta P p n ∧ theta P p n ≤ 1 := by
  have hr := rr_pos P hP n
  rw [theta_eq' P hP hp]
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  have a1 := Z_pos P hH hlam hp
  have a2 := Z_pos P hL hlam hp
  have hK : 0 < (1 - P.γ) * (rho P P.muL / rho P P.muH) ^ n * Z P P.muH p :=
    mul_pos (mul_pos (by linarith) hr) a1
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith

lemma util_mono_theta (P : Params) (hP : P.Standing) {p p' : ℕ → ℝ} (n : ℕ)
    (h : theta P p n ≤ theta P p' n) : util P p n ≤ util P p' n := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hinv : 1 / P.muH < 1 / P.muL := one_div_lt_one_div_of_lt hL hLH
  unfold util meanSojourn
  have e : ∀ t : ℝ, t / P.muH + (1 - t) / P.muL = 1 / P.muL - t * (1 / P.muL - 1 / P.muH) :=
    fun t => by field_simp; ring
  rw [e, e]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : theta P p n * (1 / P.muL - 1 / P.muH) ≤ theta P p' n * (1 / P.muL - 1 / P.muH) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  have h2 : 0 ≤ P.C * ((n : ℝ) + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

lemma utilV_mono (P : Params) (hP : P.Standing) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (n : ℕ) :
    utilV P v n ≤ utilV P w n :=
  util_mono_theta P hP n (theta_mono P hP (thr_join v hv) (thr_join w (le_trans hv hvw))
    (thr_mono hv hvw) n)

lemma Nbar_pos (P : Params) (hP : P.Standing) : 1 ≤ Nbar P := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  unfold Nbar
  apply Nat.le_floor
  push_cast
  rw [le_div_iff₀ hC]
  have h1 : P.C < P.R * P.muL := by rwa [div_lt_iff₀ hL] at hR
  have hRp : 0 < P.R := by
    by_contra h; have := not_lt.mp h; nlinarith
  nlinarith

/-- beyond `N̄ - 1` the profile does not change the law -/
lemma Z_const (P : Params) (mu : ℝ) {w : ℝ} (hw : ((Nbar P - 1 : ℕ) : ℝ) ≤ w) :
    Z P mu (thrProfile w) = Z P mu (thrProfile ((Nbar P - 1 : ℕ) : ℝ)) := by
  have h0 : (0 : ℝ) ≤ ((Nbar P - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold Z weight
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ Nbar P - 1 := by
    simp only [Finset.mem_range] at hi hj; omega
  have : (i : ℝ) ≤ ((Nbar P - 1 : ℕ) : ℝ) := by exact_mod_cast hi'
  rw [thr_one (le_trans h0 hw) (le_trans this hw), thr_one h0 this]

lemma utilV_const (P : Params) {w : ℝ} (hw : ((Nbar P - 1 : ℕ) : ℝ) ≤ w) (n : ℕ) :
    utilV P w n = utilV P ((Nbar P - 1 : ℕ) : ℝ) n := by
  unfold utilV util
  rw [theta_eq, theta_eq, Z_const P _ hw, Z_const P _ hw]

lemma utilV_le_b (P : Params) (hP : P.Standing) {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    utilV P w n ≤ utilV P ((Nbar P - 1 : ℕ) : ℝ) n := by
  rcases le_total w ((Nbar P - 1 : ℕ) : ℝ) with h | h
  · exact utilV_mono P hP hw h n
  · rw [utilV_const P h]

lemma util_Nbar_neg (P : Params) (hP : P.Standing) {p : ℕ → ℝ} (hp : IsJoinVec p) :
    util P p (Nbar P) < 0 := by
  have hm := theta_mem P hP hp (Nbar P)
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  have hinv : 1 / P.muH < 1 / P.muL := one_div_lt_one_div_of_lt hL hLH
  have hN : P.R * P.muH / P.C < (Nbar P : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [div_lt_iff₀ hC] at hN
  unfold util meanSojourn
  set t := theta P p (Nbar P)
  have e : t / P.muH + (1 - t) / P.muL = 1 / P.muH + (1 - t) * (1 / P.muL - 1 / P.muH) := by
    field_simp; ring
  rw [e]
  have h1 : 0 ≤ (1 - t) * (1 / P.muL - 1 / P.muH) := mul_nonneg (by linarith) (by linarith)
  have h2 : P.R < P.C * ((Nbar P : ℝ) + 1) * (1 / P.muH) := by
    rw [mul_one_div, lt_div_iff₀ hH]; linarith
  have h3 : 0 ≤ P.C * ((Nbar P : ℝ) + 1) := by positivity
  nlinarith [mul_nonneg h3 h1]


/-! ### Congestion effect -/

lemma cdf_eq (P : Params) (mu : ℝ) (p : ℕ → ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), stat P mu p n =
      (∑ k ∈ (Finset.range (Nbar P + 1)).filter (· ≤ m), weight P mu p k) / Z P mu p := by
  have e1 : ∑ n ∈ Finset.range (m + 1), stat P mu p n =
      ∑ n ∈ Finset.range (m + 1), if n ≤ Nbar P then weight P mu p n / Z P mu p else 0 := rfl
  rw [e1, ← Finset.sum_filter, Finset.sum_div]
  congr 1
  ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma congestion (P : Params) (hP : P.Standing) (mu : ℝ) (hmu : mu = P.muH ∨ mu = P.muL)
    {p p' : ℕ → ℝ} (hp : IsJoinVec p) (hp' : IsJoinVec p') (hle : ∀ i, p i ≤ p' i) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), stat P mu p' n ≤ ∑ n ∈ Finset.range (m + 1), stat P mu p n := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hmu0 : 0 < mu := by rcases hmu with h | h <;> rw [h] <;> linarith
  rw [cdf_eq, cdf_eq]
  set SA := (Finset.range (Nbar P + 1)).filter (· ≤ m)
  set SB := (Finset.range (Nbar P + 1)).filter (fun k => ¬ k ≤ m)
  have hZ : ∀ q, Z P mu q = (∑ k ∈ SA, weight P mu q k) + ∑ k ∈ SB, weight P mu q k :=
    fun q => (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have z1 := Z_pos P hmu0 hlam hp
  have z2 := Z_pos P hmu0 hlam hp'
  rw [div_le_div_iff₀ z2 z1, hZ p, hZ p']
  set A := ∑ k ∈ SA, weight P mu p k
  set B := ∑ k ∈ SB, weight P mu p k
  set A' := ∑ k ∈ SA, weight P mu p' k
  set B' := ∑ k ∈ SB, weight P mu p' k
  have key : A' * B ≤ A * B' := by
    simp only [A, B, A', B']
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
    simp only [SA, SB, Finset.mem_filter] at hj hk
    have hjk : j ≤ k := by omega
    have h1 := prod_cross hp hp' hle hjk
    unfold weight
    have h0 : 0 ≤ rho P mu ^ j * rho P mu ^ k :=
      mul_nonneg (pow_nonneg (div_pos hlam hmu0).le _) (pow_nonneg (div_pos hlam hmu0).le _)
    have := mul_le_mul_of_nonneg_left h1 h0
    linarith [this]
  nlinarith

/-! ### Continuity in `v` -/

lemma weight_cont (P : Params) (mu : ℝ) (n : ℕ) :
    ContinuousOn (fun v => weight P mu (thrProfile v) n) (Set.Ici 0) := by
  unfold weight
  exact continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => thr_cont i)

lemma Z_cont (P : Params) (mu : ℝ) :
    ContinuousOn (fun v => Z P mu (thrProfile v)) (Set.Ici 0) := by
  unfold Z
  exact continuousOn_finsetSum _ fun j _ => weight_cont P mu j

lemma stat_cont (P : Params) (hP : P.Standing) (mu : ℝ) (hmu : mu = P.muH ∨ mu = P.muL)
    (n : ℕ) : ContinuousOn (fun v => stat P mu (thrProfile v) n) (Set.Ici 0) := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hmu0 : 0 < mu := by rcases hmu with h | h <;> rw [h] <;> linarith
  unfold stat
  by_cases hn : n ≤ Nbar P
  · simp only [if_pos hn]
    exact (weight_cont P mu n).div (Z_cont P mu) fun v hv =>
      (Z_pos P hmu0 hlam (thr_join v hv)).ne'
  · simp only [if_neg hn]; exact continuousOn_const

lemma utilV_cont (P : Params) (hP : P.Standing) (n : ℕ) :
    ContinuousOn (fun v => utilV P v n) (Set.Ici 0) := by
  have hr := rr_pos P hP n
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  have hth : ContinuousOn (fun v => thetaV P v n) (Set.Ici 0) := by
    have : ContinuousOn (fun v => P.γ * (1 / Z P P.muH (thrProfile v)) /
      (P.γ * (1 / Z P P.muH (thrProfile v)) + (1 - P.γ) * (1 / Z P P.muL (thrProfile v)) *
        (rho P P.muL / rho P P.muH) ^ n)) (Set.Ici 0) := by
      have cH : ContinuousOn (fun v => 1 / Z P P.muH (thrProfile v)) (Set.Ici 0) :=
        continuousOn_const.div (Z_cont P _) fun v hv => (Z_pos P hH hlam (thr_join v hv)).ne'
      have cL : ContinuousOn (fun v => 1 / Z P P.muL (thrProfile v)) (Set.Ici 0) :=
        continuousOn_const.div (Z_cont P _) fun v hv => (Z_pos P hL hlam (thr_join v hv)).ne'
      refine (continuousOn_const.mul cH).div ((continuousOn_const.mul cH).add
        ((continuousOn_const.mul cL).mul continuousOn_const)) fun v hv => ?_
      have := Z_pos P hH hlam (thr_join v hv)
      have := Z_pos P hL hlam (thr_join v hv)
      have : 0 < 1 - P.γ := by linarith
      positivity
    exact this.congr fun v _ => theta_eq P _ n
  unfold utilV util
  exact continuousOn_const.sub (continuousOn_const.mul
    ((hth.div_const _).add ((continuousOn_const.sub hth).div_const _)))


/-! ### Support of the law under `p⁻(w)` -/

lemma stat_pos (P : Params) (hP : P.Standing) (mu : ℝ) (hmu : mu = P.muH ∨ mu = P.muL)
    {w : ℝ} (hw : 0 ≤ w) {n : ℕ} (hn : n ≤ Nbar P) (hnw : (n : ℝ) < w + 2) :
    0 < stat P mu (thrProfile w) n := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hmu0 : 0 < mu := by rcases hmu with h | h <;> rw [h] <;> linarith
  unfold stat
  rw [if_pos hn]
  refine div_pos (mul_pos (pow_pos (div_pos hlam hmu0) _) (Finset.prod_pos fun i hi => ?_))
    (Z_pos P hmu0 hlam (thr_join w hw))
  apply thr_pos hw
  have : i + 1 ≤ n := by simp only [Finset.mem_range] at hi; omega
  have : (i : ℝ) + 1 ≤ n := by exact_mod_cast this
  linarith

lemma stat_zero (P : Params) (mu : ℝ) {w : ℝ} (hw : 0 ≤ w) {n : ℕ} (hnw : w + 2 ≤ (n : ℝ)) :
    stat P mu (thrProfile w) n = 0 := by
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  unfold stat weight
  split_ifs
  · rw [Finset.prod_eq_zero (i := n - 1) (by simp; omega)]
    · simp
    · apply thr_zero hw
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn1]; simp
      rw [this]; linarith
  · rfl

lemma br_mem (P : Params) (p : ℕ → ℝ) (k : ℕ) : 0 ≤ bestResp P p k ∧ bestResp P p k ≤ 1 := by
  unfold bestResp; split_ifs <;> norm_num

end Aux_FCProp2

open FollowCrowd.Inference Aux_FCProp2 in
theorem solution (P : Params) (hP : P.Standing) :
    (∃ v ∈ Set.Ioo (0 : ℝ) (Nbar P), ∃ δ > 0, JPV P v < JPV P (v + δ)) ↔
      ∃ n ∈ Finset.Icc 1 (Nbar P - 1),
        ((n : ℝ) + 1) * meanSojourn P (thetaV P ((Nbar P - 1 : ℕ) : ℝ) n) ≤ P.R / P.C ∧
          P.R / P.C < ((n : ℝ) + 1) * meanSojourn P (thetaV P ((n - 2 : ℕ) : ℝ) n) := by
  classical
  have hP' := hP
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP'
  have hH : 0 < P.muH := lt_trans hL hLH
  set N := Nbar P with hNdef
  have hN1 : 1 ≤ N := Nbar_pos P hP
  set b : ℝ := ((N - 1 : ℕ) : ℝ) with hbdef
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  -- conversions of the two conditions
  have cv1 : ∀ (n : ℕ) (v : ℝ), ((n : ℝ) + 1) * meanSojourn P (thetaV P v n) ≤ P.R / P.C ↔
      0 ≤ utilV P v n := by
    intro n v
    rw [le_div_iff₀ hC]
    show _ ↔ 0 ≤ P.R - P.C * ((n : ℝ) + 1) * meanSojourn P (thetaV P v n)
    constructor <;> intro h <;> linarith
  have cv2 : ∀ (n : ℕ) (v : ℝ), P.R / P.C < ((n : ℝ) + 1) * meanSojourn P (thetaV P v n) ↔
      utilV P v n < 0 := by
    intro n v
    rw [div_lt_iff₀ hC]
    show _ ↔ P.R - P.C * ((n : ℝ) + 1) * meanSojourn P (thetaV P v n) < 0
    constructor <;> intro h <;> linarith
  -- the weight of state k under p⁻(w)
  set q : ℕ → ℝ → ℝ := fun k w =>
    P.γ * stat P P.muH (thrProfile w) k + (1 - P.γ) * stat P P.muL (thrProfile w) k with hqdef
  have hq0 : ∀ k w, 0 ≤ w → 0 ≤ q k w := by
    intro k w hw
    have := stat_nonneg P hH hlam (thr_join w hw) k
    have := stat_nonneg P hL hlam (thr_join w hw) k
    have : 0 < 1 - P.γ := by linarith
    simp only [q]; positivity
  have hJP : ∀ w, JPV P w = ∑ k ∈ Finset.range (N + 1), bestResp P (thrProfile w) k * q k w :=
    fun w => rfl
  -- utility is antitone in the state
  have hanti : ∀ w, 0 ≤ w → ∀ {j k : ℕ}, j ≤ k → utilV P w k ≤ utilV P w j := fun w hw j k hjk =>
    ((FollowCrowd.Inference.lemma_1 P hP _ (thr_join w hw)).2.antitone hjk)
  constructor
  · -- only if
    rintro ⟨v, hv, δ, hδ, hlt⟩
    by_contra hno
    push Not at hno
    have hno' : ∀ k, 1 ≤ k → k ≤ N - 1 → 0 ≤ utilV P b k → 0 ≤ utilV P ((k - 2 : ℕ) : ℝ) k := by
      intro k hk1 hk2 hk
      have := hno k (Finset.mem_Icc.2 ⟨hk1, hk2⟩) ((cv1 k b).2 hk)
      exact not_lt.mp (fun h => (not_lt.mpr this) ((cv2 k _).2 h))
    set s := Nat.findGreatest (fun k => k = 0 ∨ 0 ≤ utilV P b k) N with hsdef
    have hsN : s ≤ N := Nat.findGreatest_le N
    have hs : ∀ k ≤ N, (k = 0 ∨ 0 ≤ utilV P b k) ↔ k ≤ s := by
      intro k hk
      constructor
      · intro h; exact Nat.le_findGreatest hk h
      · intro hks
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · exact Or.inl h0
        · right
          have hsp : s = 0 ∨ 0 ≤ utilV P b s :=
            Nat.findGreatest_spec (P := fun k => k = 0 ∨ 0 ≤ utilV P b k) (Nat.zero_le N)
              (Or.inl rfl)
          rcases hsp with h | h
          · omega
          · exact le_trans h (hanti b hb0 hks)
    have hterm : ∀ w, 0 ≤ w → ∀ k ∈ Finset.range (N + 1),
        bestResp P (thrProfile w) k * q k w = if k ≤ s then q k w else 0 := by
      intro w hw k hk
      have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
      by_cases hks : k ≤ s
      · rw [if_pos hks]
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · simp [bestResp, h0]
        · have hub : 0 ≤ utilV P b k := by
            rcases (hs k hkN).2 hks with h | h
            · omega
            · exact h
          have hkN' : k ≠ N := by
            intro hkN'
            have : utilV P b N < 0 := util_Nbar_neg P hP (thr_join b hb0)
            rw [← hkN'] at this
            exact absurd hub (not_le.mpr this)
          have ha := hno' k hpos (by omega) hub
          set a : ℝ := ((k - 2 : ℕ) : ℝ)
          by_cases hwa : a ≤ w
          · have := utilV_mono P hP (Nat.cast_nonneg _) hwa k
            have hbr : bestResp P (thrProfile w) k = 1 := by
              unfold bestResp; exact if_pos (Or.inr (le_trans ha this))
            rw [hbr, one_mul]
          · push Not at hwa
            have hk3 : (k : ℝ) ≥ w + 2 := by
              have : k - 2 + 2 ≤ k := by
                have : 0 < k - 2 := by
                  by_contra hc
                  have : k - 2 = 0 := by omega
                  simp only [a, this, Nat.cast_zero] at hwa; linarith
                omega
              have : (((k - 2 : ℕ) : ℝ)) + 2 ≤ k := by exact_mod_cast this
              linarith
            have hq : q k w = 0 := by
              simp only [q, stat_zero P _ hw hk3]; ring
            rw [hq, mul_zero]
      · rw [if_neg hks]
        have hk0 : k ≠ 0 := by omega
        have hub : utilV P b k < 0 := by
          by_contra hc
          exact hks ((hs k hkN).1 (Or.inr (not_lt.mp hc)))
        have := utilV_le_b P hP hw k
        have hbr : bestResp P (thrProfile w) k = 0 := by
          unfold bestResp
          rw [if_neg]
          rintro (h | h)
          · exact hk0 h
          · exact absurd (lt_of_le_of_lt this hub) (not_lt.mpr h)
        rw [hbr, zero_mul]
    have hJPs : ∀ w, 0 ≤ w → JPV P w =
        P.γ * ∑ k ∈ Finset.range (s + 1), stat P P.muH (thrProfile w) k +
          (1 - P.γ) * ∑ k ∈ Finset.range (s + 1), stat P P.muL (thrProfile w) k := by
      intro w hw
      rw [hJP, Finset.sum_congr rfl (hterm w hw), ← Finset.sum_filter]
      have : (Finset.range (N + 1)).filter (· ≤ s) = Finset.range (s + 1) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [this, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hv0 : 0 ≤ v := le_of_lt hv.1
    have hvd : v ≤ v + δ := by linarith
    have c1 := congestion P hP P.muH (Or.inl rfl) (thr_join v hv0) (thr_join (v + δ) (by linarith))
      (thr_mono hv0 hvd) s
    have c2 := congestion P hP P.muL (Or.inr rfl) (thr_join v hv0) (thr_join (v + δ) (by linarith))
      (thr_mono hv0 hvd) s
    rw [hJPs v hv0, hJPs (v + δ) (by linarith)] at hlt
    have : 0 < 1 - P.γ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left c1 hg0.le, mul_le_mul_of_nonneg_left c2 this.le]
  · -- if
    rintro ⟨n, hn, h1, h2⟩
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn2 : n ≤ N - 1 := (Finset.mem_Icc.1 hn).2
    set a : ℝ := ((n - 2 : ℕ) : ℝ) with hadef
    have ha0 : 0 ≤ a := Nat.cast_nonneg _
    have hab : a ≤ b := by
      have : n - 2 ≤ N - 1 := by omega
      show ((n - 2 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ)
      exact_mod_cast this
    have hna : (n : ℝ) ≤ a + 2 := by
      have : n ≤ n - 2 + 2 := by omega
      have : (n : ℝ) ≤ ((n - 2 : ℕ) : ℝ) + 2 := by exact_mod_cast this
      linarith
    have hub : 0 ≤ utilV P b n := (cv1 n b).1 h1
    have hua : utilV P a n < 0 := (cv2 n a).1 h2
    set S : Set ℝ := Set.Icc a b ∩ (fun w => utilV P w n) ⁻¹' Set.Ici 0 with hSdef
    have hcont : ContinuousOn (fun w => utilV P w n) (Set.Icc a b) :=
      (utilV_cont P hP n).mono fun w hw => le_trans ha0 hw.1
    have hScl : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hSne : S.Nonempty := ⟨b, ⟨hab, le_refl _⟩, hub⟩
    have hSbdd : BddBelow S := ⟨a, fun w hw => hw.1.1⟩
    set vs := sInf S with hvsdef
    have hvsS : vs ∈ S := hScl.csInf_mem hSne hSbdd
    have hvsa : a < vs := by
      rcases lt_or_eq_of_le hvsS.1.1 with h | h
      · exact h
      · exfalso
        have := hvsS.2
        simp only [Set.mem_preimage, Set.mem_Ici] at this
        rw [← h] at this; linarith
    have hvsb : vs ≤ b := hvsS.1.2
    have hvs0 : 0 ≤ vs := le_trans ha0 hvsa.le
    have huvs : 0 ≤ utilV P vs n := hvsS.2
    have hbelow : ∀ w, a ≤ w → w < vs → utilV P w n < 0 := by
      intro w hw1 hw2
      by_contra hc
      have hwS : w ∈ S := ⟨⟨hw1, by linarith⟩, not_lt.mp hc⟩
      have := csInf_le hSbdd hwS
      linarith
    -- the mass of state n at vs is positive
    have hnN : n ≤ N := by omega
    have hqn : 0 < q n vs := by
      have := stat_pos P hP P.muH (Or.inl rfl) hvs0 hnN (by linarith)
      have := stat_nonneg P hL hlam (thr_join vs hvs0) n
      have : 0 < 1 - P.γ := by linarith
      simp only [q]; positivity
    -- continuity of the CDF up to n-1
    set G : ℝ → ℝ := fun w => ∑ k ∈ Finset.range n, q k w with hGdef
    have hGc : ContinuousOn G (Set.Ici 0) := by
      refine continuousOn_finsetSum _ fun k _ => ?_
      exact (continuousOn_const.mul (stat_cont P hP _ (Or.inl rfl) k)).add
        (continuousOn_const.mul (stat_cont P hP _ (Or.inr rfl) k))
    have hGw := (Metric.continuousWithinAt_iff.1 (hGc vs (Set.mem_Ici.2 hvs0))) (q n vs) hqn
    obtain ⟨ε, hε, hεG⟩ := hGw
    set w1 := max ((a + vs) / 2) (vs - ε / 2) with hw1def
    have hw1a : a < w1 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hw1v : w1 < vs := max_lt (by linarith) (by linarith)
    have hw10 : 0 ≤ w1 := le_trans ha0 hw1a.le
    have hdist : dist w1 vs < ε := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have := le_max_right ((a + vs) / 2) (vs - ε / 2)
      linarith
    have hGG := hεG (Set.mem_Ici.2 hw10) hdist
    rw [Real.dist_eq] at hGG
    have hGG' := (abs_lt.1 hGG).2
    -- JP at w1 is at most G w1
    have hJ1 : JPV P w1 ≤ G w1 := by
      rw [hJP, ← Finset.sum_range_add_sum_Ico _ (show n ≤ N + 1 by omega)]
      have hz : ∑ k ∈ Finset.Ico n (N + 1), bestResp P (thrProfile w1) k * q k w1 = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hk' : n ≤ k := (Finset.mem_Ico.1 hk).1
        have hbr : bestResp P (thrProfile w1) k = 0 := by
          unfold bestResp
          rw [if_neg]
          rintro (h | h)
          · omega
          · have h' : 0 ≤ utilV P w1 k := h
            have := hanti w1 hw10 hk'
            have := hbelow w1 hw1a.le hw1v
            linarith
        rw [hbr, zero_mul]
      rw [hz, add_zero]
      refine Finset.sum_le_sum fun k _ => ?_
      have := br_mem P (thrProfile w1) k
      have := hq0 k w1 hw10
      nlinarith
    -- JP at vs is at least G vs + q n vs
    have hJ2 : G vs + q n vs ≤ JPV P vs := by
      rw [hJP, ← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ N + 1 by omega)]
      have hnn : 0 ≤ ∑ k ∈ Finset.Ico (n + 1) (N + 1), bestResp P (thrProfile vs) k * q k vs :=
        Finset.sum_nonneg fun k _ => mul_nonneg (br_mem P _ k).1 (hq0 k vs hvs0)
      have heq : ∑ k ∈ Finset.range (n + 1), bestResp P (thrProfile vs) k * q k vs =
          ∑ k ∈ Finset.range (n + 1), q k vs := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ n := by simp only [Finset.mem_range] at hk; omega
        have hbr : bestResp P (thrProfile vs) k = 1 := by
          unfold bestResp
          exact if_pos (Or.inr (le_trans huvs (hanti vs hvs0 hk')))
        rw [hbr, one_mul]
      rw [heq, Finset.sum_range_succ]
      linarith
    refine ⟨w1, ⟨lt_of_le_of_lt ha0 hw1a, ?_⟩, vs - w1, by linarith, ?_⟩
    · have : b ≤ (N : ℝ) - 1 := by
        rw [hbdef, Nat.cast_sub hN1]; simp
      linarith
    · rw [show w1 + (vs - w1) = vs by ring]
      linarith
