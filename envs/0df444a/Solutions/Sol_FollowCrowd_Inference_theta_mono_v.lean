-- Prove2me | solution 1 for FollowCrowd.Inference.theta_mono_v
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:04:46.757613+00:00
-- url     : https://prove2.me/submissions/be491eca-fe92-45d0-92be-7c8044adf22a

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

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


/-! ### Strict inference effect -/

lemma Z_cross_strict (P : Params) (hP : P.Standing) {p p' : ℕ → ℝ} (hp : IsJoinVec p)
    (hp' : IsJoinVec p') (hle : ∀ i, p i ≤ p' i) {n' : ℕ} (hn' : n' < Nbar P)
    (hc : 0 < ∏ i ∈ Finset.range n', p i) (hlt : p n' < p' n') :
    Z P P.muL p * Z P P.muH p' < Z P P.muL p' * Z P P.muH p := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  set a := rho P P.muL
  set b := rho P P.muH
  have hb : 0 < b := div_pos hlam hH
  have hab : b < a := div_lt_div_of_pos_left hlam hL hLH
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
  rw [eL, eR, ← sub_pos, ← Finset.sum_sub_distrib]
  set f : ℕ → ℕ → ℝ := fun j k => a ^ j * b ^ k * (c' j * c k) - a ^ j * b ^ k * (c j * c' k)
  have hsum : ∑ j ∈ S, ∑ k ∈ S, f j k = ∑ j ∈ S, ∑ k ∈ S, f k j := Finset.sum_comm
  have e : ∀ j k, f j k + f k j = (a ^ k * b ^ j - a ^ j * b ^ k) * (c j * c' k - c' j * c k) := by
    intro j k; simp only [f]; ring
  have key : ∀ j k, 0 ≤ f j k + f k j := by
    have main : ∀ j k, j ≤ k → 0 ≤ f j k + f k j := by
      intro j k hjk
      have h1 := prod_cross hp hp' hle hjk
      have h2 : a ^ j * b ^ k ≤ a ^ k * b ^ j := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
        rw [pow_add, pow_add]
        have : b ^ d ≤ a ^ d := pow_le_pow_left₀ hb.le hab.le d
        have ha0 : 0 ≤ a ^ j := pow_nonneg (le_trans hb.le hab.le) j
        have hb0 : 0 ≤ b ^ j := pow_nonneg hb.le j
        calc a ^ j * (b ^ j * b ^ d) = (a ^ j * b ^ j) * b ^ d := by ring
          _ ≤ (a ^ j * b ^ j) * a ^ d := mul_le_mul_of_nonneg_left this (mul_nonneg ha0 hb0)
          _ = a ^ j * a ^ d * b ^ j := by ring
      rw [e]
      exact mul_nonneg (by linarith) (by simp only [c, c'] at h1 ⊢; linarith)
    intro j k
    rcases le_total j k with h | h
    · exact main j k h
    · have := main k j h; linarith
  have kpos : 0 < f n' (n' + 1) + f (n' + 1) n' := by
    rw [e]
    have hc' : c n' ≤ c' n' :=
      Finset.prod_le_prod (fun i _ => (hp.2 i).1) (fun i _ => hle i)
    have h1 : 0 < c n' * c' (n' + 1) - c' n' * c (n' + 1) := by
      simp only [c, c', Finset.prod_range_succ]
      have : 0 < c n' * c' n' * (p' n' - p n') :=
        mul_pos (mul_pos hc (lt_of_lt_of_le hc hc')) (by linarith)
      simp only [c, c'] at this
      nlinarith
    have h2 : 0 < a ^ (n' + 1) * b ^ n' - a ^ n' * b ^ (n' + 1) := by
      rw [pow_succ, pow_succ]
      have : 0 < a ^ n' * b ^ n' * (a - b) :=
        mul_pos (mul_pos (pow_pos (by linarith) _) (pow_pos hb _)) (by linarith)
      nlinarith
    exact mul_pos h2 h1
  have : 2 * ∑ j ∈ S, ∑ k ∈ S, f j k = ∑ j ∈ S, ∑ k ∈ S, (f j k + f k j) := by
    rw [two_mul]
    conv_lhs => arg 2; rw [hsum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
  have hmem : n' ∈ S := by simp only [S, Finset.mem_range]; omega
  have hmem' : n' + 1 ∈ S := by simp only [S, Finset.mem_range]; omega
  have h3 : 0 < ∑ j ∈ S, ∑ k ∈ S, (f j k + f k j) := by
    refine Finset.sum_pos' (fun j _ => Finset.sum_nonneg fun k _ => key j k) ⟨n', hmem, ?_⟩
    exact Finset.sum_pos' (fun k _ => key n' k) ⟨n' + 1, hmem', kpos⟩
  have h4 : 0 < ∑ j ∈ S, ∑ k ∈ S, f j k := by linarith
  simpa [f] using h4

lemma theta_strict (P : Params) (hP : P.Standing) {p p' : ℕ → ℝ} (hp : IsJoinVec p)
    (hp' : IsJoinVec p') (hle : ∀ i, p i ≤ p' i) {n' : ℕ} (hn' : n' < Nbar P)
    (hc : 0 < ∏ i ∈ Finset.range n', p i) (hlt : p n' < p' n') (n : ℕ) :
    theta P p n < theta P p' n := by
  have hc := Z_cross_strict P hP hp hp' hle hn' hc hlt
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
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : P.γ * K * (Z P P.muL p * Z P P.muH p') < P.γ * K * (Z P P.muL p' * Z P P.muH p) :=
    mul_lt_mul_of_pos_left hc (by positivity)
  nlinarith

lemma util_strict_theta (P : Params) (hP : P.Standing) {p p' : ℕ → ℝ} (n : ℕ)
    (h : theta P p n < theta P p' n) : util P p n < util P p' n := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hinv : 1 / P.muH < 1 / P.muL := one_div_lt_one_div_of_lt hL hLH
  unfold util meanSojourn
  have e : ∀ t : ℝ, t / P.muH + (1 - t) / P.muL = 1 / P.muL - t * (1 / P.muL - 1 / P.muH) :=
    fun t => by field_simp; ring
  rw [e, e]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : theta P p n * (1 / P.muL - 1 / P.muH) < theta P p' n * (1 / P.muL - 1 / P.muH) :=
    mul_lt_mul_of_pos_right h (by linarith)
  have h2 : 0 < P.C * ((n : ℝ) + 1) := by positivity
  nlinarith [mul_lt_mul_of_pos_left h1 h2]

lemma thetaV_strict (P : Params) (hP : P.Standing) (n : ℕ) :
    StrictMonoOn (fun v => thetaV P v n) (Set.Icc 0 ((Nbar P - 1 : ℕ) : ℝ)) := by
  intro v hv w hw hvw
  have hv0 : 0 ≤ v := hv.1
  set k := ⌊v⌋₊
  have hk1 : (k : ℝ) ≤ v := Nat.floor_le hv0
  have hk2 : v < (k : ℝ) + 1 := Nat.lt_floor_add_one v
  have hkN : k + 1 < Nbar P := by
    have hN1 := Nbar_pos P hP
    have : (k : ℝ) < ((Nbar P - 1 : ℕ) : ℝ) := by linarith [hw.2]
    have : k < Nbar P - 1 := by exact_mod_cast this
    omega
  refine theta_strict P hP (thr_join v hv0) (thr_join w (by linarith)) (thr_mono hv0 hvw.le)
    hkN ?_ ?_ n
  · refine Finset.prod_pos fun i hi => thr_pos hv0 ?_
    have : i ≤ k := by simp only [Finset.mem_range] at hi; omega
    have : (i : ℝ) ≤ k := by exact_mod_cast this
    linarith
  · rw [thr_eq v hv0, thr_eq w (by linarith)]
    push_cast
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    exact lt_max_of_lt_right (lt_min (by linarith) (by linarith))

lemma ms_strict (P : Params) (hP : P.Standing) {t t' : ℝ} (h : t < t') :
    meanSojourn P t' < meanSojourn P t := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hinv : 1 / P.muH < 1 / P.muL := one_div_lt_one_div_of_lt hL hLH
  unfold meanSojourn
  have e : ∀ t : ℝ, t / P.muH + (1 - t) / P.muL = 1 / P.muL - t * (1 / P.muL - 1 / P.muH) :=
    fun t => by field_simp; ring
  rw [e, e]
  nlinarith [mul_lt_mul_of_pos_right h (sub_pos.2 hinv)]

end Aux_FCProp2

open FollowCrowd.Inference Aux_FCProp2 in
theorem solution (P : Params) (hP : P.Standing) (n : ℕ) :
    StrictMonoOn (fun v => thetaV P v n) (Set.Icc 0 ((Nbar P - 1 : ℕ) : ℝ)) ∧
    (2 ≤ Nbar P →
      ((n : ℝ) + 1) * meanSojourn P (thetaV P ((Nbar P - 1 : ℕ) : ℝ) n) <
        ((n : ℝ) + 1) * meanSojourn P (thetaV P 0 n)) := by
  refine ⟨thetaV_strict P hP n, fun h2 => ?_⟩
  have hb : (0 : ℝ) < ((Nbar P - 1 : ℕ) : ℝ) := by
    have : 0 < Nbar P - 1 := by omega
    exact_mod_cast this
  have := thetaV_strict P hP n ⟨le_refl 0, hb.le⟩ ⟨hb.le, le_refl _⟩ hb
  have := ms_strict P hP this
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact mul_lt_mul_of_pos_left this hn
