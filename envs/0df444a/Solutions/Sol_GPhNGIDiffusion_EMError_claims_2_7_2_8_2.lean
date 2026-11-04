-- Prove2me | solution 2 for GPhNGIDiffusion.EMError.claims_2_7_2_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T17:56:54.387535+00:00
-- url     : https://prove2.me/submissions/0d2ad6f1-7ef0-4f86-b57e-472cd135b003
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GPhNGIDiffusion_EMError_proposition_2_1_unique_moments
import Theorems.Thm_GPhNGIDiffusion_EMError_lemma_2_2

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EMErrClaimsAux
open GPhNGIDiffusion.EMError

variable {d : ℕ}

lemma sum_single (u : EthierKurtz.SDEState d) : ∑ i, u i • EuclideanSpace.single i (1:ℝ) = u := by
  have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr u
  simpa using this


lemma mv_apply (σ : Matrix (Fin d) (Fin d) ℝ) (z : EthierKurtz.SDEState d) (i : Fin d) :
    mv σ z i = inner ℝ (WithLp.toLp 2 (fun k => σ i k) : EthierKurtz.SDEState d) z := by
  simp [mv, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]



lemma coord_le (x : EthierKurtz.SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i


lemma drift_bound (M : Model d) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (w : EthierKurtz.SDEState d) (i : Fin d), |M.drift w i| ≤ G * (1 + ‖w‖) := by
  set v := Matrix.mulVec (M.R - M.α • (1 : Matrix (Fin d) (Fin d) ℝ)) M.p with hv
  let Gi : Fin d → ℝ := fun i => |M.β| * |M.p i| + ∑ j, |M.R i j| + (d : ℝ) * |v i|
  have hGi : ∀ i, 0 ≤ Gi i := fun i => by positivity
  refine ⟨∑ i, Gi i, Finset.sum_nonneg (fun i _ => hGi i), fun w i => ?_⟩
  have hle : Gi i ≤ ∑ i, Gi i := Finset.single_le_sum (fun i _ => hGi i) (Finset.mem_univ i)
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hcoord : M.drift w i = -(M.β * M.p i) - ∑ j, M.R i j * w j
      + max 0 (∑ k, w k) * v i := by
    simp [Model.drift, hv, Matrix.mulVec, dotProduct]
  have h1 : |∑ j, M.R i j * w j| ≤ (∑ j, |M.R i j|) * ‖w‖ := by
    calc |∑ j, M.R i j * w j| ≤ ∑ j, |M.R i j * w j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |M.R i j| * ‖w‖ := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (coord_le w j) (abs_nonneg _))
      _ = (∑ j, |M.R i j|) * ‖w‖ := by rw [Finset.sum_mul]
  have h2 : |max 0 (∑ k, w k)| ≤ (d : ℝ) * ‖w‖ := by
    have : |∑ k, w k| ≤ (d : ℝ) * ‖w‖ := by
      calc |∑ k, w k| ≤ ∑ k, |w k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin d, ‖w‖ := Finset.sum_le_sum (fun k _ => coord_le w k)
        _ = (d : ℝ) * ‖w‖ := by simp
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (by positivity) (le_trans (le_abs_self _) this)
  have h3 : |max 0 (∑ k, w k) * v i| ≤ (d : ℝ) * ‖w‖ * |v i| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have h4 : |M.β * M.p i| = |M.β| * |M.p i| := abs_mul _ _
  have key : |M.drift w i| ≤ Gi i * (1 + ‖w‖) := by
    rw [hcoord]
    have t1 := abs_add_le (-(M.β * M.p i) - ∑ j, M.R i j * w j) (max 0 (∑ k, w k) * v i)
    have t2 := abs_sub (-(M.β * M.p i)) (∑ j, M.R i j * w j)
    rw [abs_neg] at t2
    have e1 : 0 ≤ |M.β| * |M.p i| * ‖w‖ := by positivity
    have e2 : 0 ≤ ∑ j, |M.R i j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have e3 : 0 ≤ (d : ℝ) * |v i| := by positivity
    simp only [Gi]
    nlinarith
  calc |M.drift w i| ≤ Gi i * (1 + ‖w‖) := key
    _ ≤ (∑ i, Gi i) * (1 + ‖w‖) := mul_le_mul_of_nonneg_right hle (by positivity)


lemma norm_le_sum_abs (x : EthierKurtz.SDEState d) : ‖x‖ ≤ ∑ i, |x i| := by
  conv_lhs => rw [← sum_single x]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_)))
  rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]

noncomputable def Sσ (σ : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ‖(WithLp.toLp 2 (fun k => σ i k) : EthierKurtz.SDEState d)‖

lemma Sσ_nonneg (σ : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ Sσ σ :=
  Finset.sum_nonneg (fun i _ => norm_nonneg _)

lemma mv_norm_le (σ : Matrix (Fin d) (Fin d) ℝ) (z : EthierKurtz.SDEState d) :
    ‖mv σ z‖ ≤ Sσ σ * ‖z‖ := by
  refine (norm_le_sum_abs _).trans ?_
  rw [Sσ, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [mv_apply]
  exact abs_real_inner_le_norm _ _

lemma drift_norm (M : Model d) (G : ℝ) (hG : ∀ w i, |M.drift w i| ≤ G * (1 + ‖w‖))
    (w : EthierKurtz.SDEState d) : ‖M.drift w‖ ≤ d * G * (1 + ‖w‖) := by
  refine (norm_le_sum_abs _).trans ?_
  calc ∑ i, |M.drift w i| ≤ ∑ _i : Fin d, G * (1 + ‖w‖) := Finset.sum_le_sum (fun i _ => hG w i)
    _ = d * G * (1 + ‖w‖) := by simp; ring

lemma sumuu_bound (u : EthierKurtz.SDEState d) (D : Fin d → Fin d → ℝ) (L : ℝ)
    (hD : ∀ i j, |D i j| ≤ L) : |∑ i, ∑ j, u i * u j * D i j| ≤ d * d * ‖u‖ ^ 2 * L := by
  calc |∑ i, ∑ j, u i * u j * D i j| ≤ ∑ i, |∑ j, u i * u j * D i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |u i * u j * D i j| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, ‖u‖ * ‖u‖ * L := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        rw [abs_mul, abs_mul]
        have := coord_le u i; have := coord_le u j
        gcongr
        exact hD i j
    _ = d * d * ‖u‖ ^ 2 * L := by simp; ring

lemma J_bound (f : EthierKurtz.SDEState d → ℝ) (w u : EthierKurtz.SDEState d) (K : ℝ)
    (hK : ∀ r r' : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ r' → r' ≤ 1 →
      |∑ i, ∑ j, u i * u j * (partial2 f i j (w + (r' * r) • u) - partial2 f i j w)| ≤ K) :
    |∫ r in (0 : ℝ)..1, ∫ r' in (0 : ℝ)..1,
        r * ∑ i, ∑ j, u i * u j * (partial2 f i j (w + (r' * r) • u) - partial2 f i j w)| ≤ K := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (C := K)
    (f := fun r => ∫ r' in (0 : ℝ)..1,
        r * ∑ i, ∑ j, u i * u j * (partial2 f i j (w + (r' * r) • u) - partial2 f i j w))
    (fun r hr => by
      rw [Set.uIoc_of_le zero_le_one] at hr
      have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (C := K)
        (f := fun r' => r * ∑ i, ∑ j, u i * u j *
          (partial2 f i j (w + (r' * r) • u) - partial2 f i j w))
        (fun r' hr' => by
          rw [Set.uIoc_of_le zero_le_one] at hr'
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr.1.le]
          have := hK r r' hr.1.le hr.2 hr'.1.le hr'.2
          have : 0 ≤ |∑ i, ∑ j, u i * u j * (partial2 f i j (w + (r' * r) • u) - partial2 f i j w)| :=
            abs_nonneg _
          nlinarith [hr.2])
      simpa using h2)
  simpa using h

lemma one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + t ^ n) := le_mul_of_one_le_right (by positivity)
          (by have : 0 ≤ t ^ n := by positivity
              linarith)
  · calc (1 + t) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * t ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + t ^ n) := by gcongr; linarith


/-- The remainder `J` of the claims, for a general `f`. -/
noncomputable def Jc (f : EthierKurtz.SDEState d → ℝ) (w u : EthierKurtz.SDEState d) : ℝ :=
  ∫ r in (0 : ℝ)..1, ∫ r' in (0 : ℝ)..1,
    r * ∑ i, ∑ j, u i * u j * (partial2 f i j (w + (r' * r) • u) - partial2 f i j w)

lemma rpow_le_one_add_pow3 (x : ℝ) (hx : 0 ≤ x) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 3) :
    x ^ p ≤ 1 + x ^ 3 := by
  rcases le_total x 1 with h | h
  · have : x ^ p ≤ 1 := Real.rpow_le_one hx h hp0
    have : 0 ≤ x ^ 3 := by positivity
    linarith
  · have : x ^ p ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hp
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    linarith

lemma one_add_pow4_le (t : ℝ) (ht : 0 ≤ t) : 1 + t ^ 4 ≤ (1 + t) ^ 4 := by
  have : (1 + t) ^ 4 = 1 + t ^ 4 + (4 * t + 6 * t ^ 2 + 4 * t ^ 3) := by ring
  rw [this]
  have : 0 ≤ 4 * t + 6 * t ^ 2 + 4 * t ^ 3 := by positivity
  linarith

lemma sqrt_rpow (η : ℝ) (hη : 0 ≤ η) (p : ℝ) : Real.sqrt η ^ p = η ^ (p / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hη]; congr 1; ring

lemma ptA (f : EthierKurtz.SDEState d → ℝ) (C ς : ℝ) (hC : 0 < C) (hς0 : 0 < ς) (hς1 : ς < 1)
    (hHol : ∀ (x y : EthierKurtz.SDEState d), ‖y - x‖ < 1 → ∀ i j : Fin d,
      |partial2 f i j y - partial2 f i j x| ≤ C * (1 + ‖x‖ ^ 4) * ‖y - x‖ ^ (1 - ς))
    (w δ : EthierKurtz.SDEState d) (hδ : ‖δ‖ < 1) (η M0 T : ℝ) (hη : 0 < η)
    (hM0 : 0 ≤ M0) (hT1 : 1 ≤ T) (ht : 1 + ‖w‖ ≤ T) (hδb : ‖δ‖ ≤ Real.sqrt η * (M0 * T)) :
    |Jc f w δ| ≤ d * d * C * (1 + M0 ^ 3) * η ^ ((3 - ς) / 2) * T ^ 7 := by
  have hJ := J_bound f w δ (d * d * ‖δ‖ ^ 2 * (C * (1 + ‖w‖ ^ 4) * ‖δ‖ ^ (1 - ς)))
    (fun r r' hr0 hr1 hr'0 hr'1 => sumuu_bound δ _ _ (fun i j => by
      have hy : ‖(w + (r' * r) • δ) - w‖ ≤ ‖δ‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr'0 hr0)]
        exact mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ hr'1 hr0 hr1)
      calc |partial2 f i j (w + (r' * r) • δ) - partial2 f i j w|
          ≤ C * (1 + ‖w‖ ^ 4) * ‖(w + (r' * r) • δ) - w‖ ^ (1 - ς) :=
            hHol w _ (lt_of_le_of_lt hy hδ) i j
        _ ≤ C * (1 + ‖w‖ ^ 4) * ‖δ‖ ^ (1 - ς) := by
            gcongr))
  refine hJ.trans ?_
  set n := ‖δ‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hT0 : 0 ≤ T := by linarith
  have e1 : n ^ 2 * n ^ (1 - ς) = n ^ (3 - ς) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add' hn0 (by norm_num; linarith)]
    congr 1; push_cast; ring
  have h2 : n ^ (3 - ς) ≤ η ^ ((3 - ς) / 2) * ((1 + M0 ^ 3) * T ^ 3) := by
    calc n ^ (3 - ς) ≤ (Real.sqrt η * (M0 * T)) ^ (3 - ς) :=
          Real.rpow_le_rpow hn0 hδb (by linarith)
      _ = η ^ ((3 - ς) / 2) * (M0 * T) ^ (3 - ς) := by
          rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), sqrt_rpow η hη.le]
      _ ≤ η ^ ((3 - ς) / 2) * (1 + (M0 * T) ^ 3) := by
          gcongr
          exact rpow_le_one_add_pow3 _ (by positivity) _ (by linarith) (by linarith)
      _ ≤ η ^ ((3 - ς) / 2) * ((1 + M0 ^ 3) * T ^ 3) := by
          gcongr
          have : 1 ≤ T ^ 3 := one_le_pow₀ hT1
          have : 0 ≤ M0 ^ 3 := by positivity
          rw [mul_pow]; nlinarith
  have h3 : 1 + ‖w‖ ^ 4 ≤ T ^ 4 :=
    (one_add_pow4_le _ (norm_nonneg _)).trans (pow_le_pow_left₀ (by positivity) ht 4)
  have hηp : 0 ≤ η ^ ((3 - ς) / 2) := by positivity
  calc (d : ℝ) * d * n ^ 2 * (C * (1 + ‖w‖ ^ 4) * n ^ (1 - ς))
      = d * d * C * (1 + ‖w‖ ^ 4) * (n ^ 2 * n ^ (1 - ς)) := by ring
    _ = d * d * C * (1 + ‖w‖ ^ 4) * n ^ (3 - ς) := by rw [e1]
    _ ≤ d * d * C * T ^ 4 * (η ^ ((3 - ς) / 2) * ((1 + M0 ^ 3) * T ^ 3)) := by
        gcongr
    _ = d * d * C * (1 + M0 ^ 3) * η ^ ((3 - ς) / 2) * T ^ 7 := by ring

lemma ptB (f : EthierKurtz.SDEState d → ℝ) (C : ℝ) (hC : 0 < C)
    (hQ : ∀ (x : EthierKurtz.SDEState d) (i j : Fin d), |partial2 f i j x| ≤ C * (1 + ‖x‖ ^ 3))
    (w δ : EthierKurtz.SDEState d) (hδ : 1 ≤ ‖δ‖) (η M0 T : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hM0 : 0 ≤ M0) (hT1 : 1 ≤ T) (ht : 1 + ‖w‖ ≤ T) (hδb : ‖δ‖ ≤ Real.sqrt η * (M0 * T)) :
    |Jc f w δ| ≤ 2 * d * d * C * M0 ^ 3 * (1 + (1 + M0) ^ 3) * η ^ (3 / 2 : ℝ) * T ^ 7 := by
  set n := ‖δ‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hT0 : 0 ≤ T := by linarith
  have hJ := J_bound f w δ (d * d * n ^ 2 * (2 * C * (1 + (‖w‖ + n) ^ 3)))
    (fun r r' hr0 hr1 hr'0 hr'1 => sumuu_bound δ _ _ (fun i j => by
      have hy : ‖w + (r' * r) • δ‖ ≤ ‖w‖ + n := by
        refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr'0 hr0)]
        exact mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ hr'1 hr0 hr1)
      have h1 := hQ (w + (r' * r) • δ) i j
      have h2 := hQ w i j
      have h3 : ‖w + (r' * r) • δ‖ ^ 3 ≤ (‖w‖ + n) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) hy 3
      have h4 : ‖w‖ ^ 3 ≤ (‖w‖ + n) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) (by linarith) 3
      calc |partial2 f i j (w + (r' * r) • δ) - partial2 f i j w|
          ≤ |partial2 f i j (w + (r' * r) • δ)| + |partial2 f i j w| := abs_sub _ _
        _ ≤ C * (1 + ‖w + (r' * r) • δ‖ ^ 3) + C * (1 + ‖w‖ ^ 3) := add_le_add h1 h2
        _ ≤ 2 * C * (1 + (‖w‖ + n) ^ 3) := by nlinarith))
  refine hJ.trans ?_
  have hsq : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη1
  have hn3 : n ^ 3 ≤ η ^ (3 / 2 : ℝ) * (M0 ^ 3 * T ^ 3) := by
    calc n ^ 3 ≤ (Real.sqrt η * (M0 * T)) ^ 3 := pow_le_pow_left₀ hn0 hδb 3
      _ = Real.sqrt η ^ ((3 : ℕ) : ℝ) * (M0 ^ 3 * T ^ 3) := by rw [Real.rpow_natCast]; ring
      _ = η ^ (3 / 2 : ℝ) * (M0 ^ 3 * T ^ 3) := by rw [sqrt_rpow η hη.le]; norm_num
  have hn2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hδ (by norm_num)
  have htn : ‖w‖ + n ≤ (1 + M0) * T := by
    have : n ≤ M0 * T := hδb.trans (by
      have : 0 ≤ M0 * T := by positivity
      nlinarith)
    nlinarith
  have h5 : 1 + (‖w‖ + n) ^ 3 ≤ (1 + (1 + M0) ^ 3) * T ^ 3 := by
    have : (‖w‖ + n) ^ 3 ≤ ((1 + M0) * T) ^ 3 :=
      pow_le_pow_left₀ (by positivity) htn 3
    have : 1 ≤ T ^ 3 := one_le_pow₀ hT1
    rw [mul_pow] at *; nlinarith
  have hηp : 0 ≤ η ^ (3 / 2 : ℝ) := by positivity
  have hT67 : T ^ 6 ≤ T ^ 7 := pow_le_pow_right₀ hT1 (by norm_num)
  calc (d : ℝ) * d * n ^ 2 * (2 * C * (1 + (‖w‖ + n) ^ 3))
      ≤ d * d * n ^ 3 * (2 * C * ((1 + (1 + M0) ^ 3) * T ^ 3)) := by gcongr
    _ ≤ d * d * (η ^ (3 / 2 : ℝ) * (M0 ^ 3 * T ^ 3)) * (2 * C * ((1 + (1 + M0) ^ 3) * T ^ 3)) := by
        gcongr
    _ = 2 * d * d * C * M0 ^ 3 * (1 + (1 + M0) ^ 3) * η ^ (3 / 2 : ℝ) * T ^ 6 := by ring
    _ ≤ 2 * d * d * C * M0 ^ 3 * (1 + (1 + M0) ^ 3) * η ^ (3 / 2 : ℝ) * T ^ 7 := by gcongr


lemma delta_bound (M : Model d) (G : ℝ) (hG0 : 0 ≤ G) (hG : ∀ w i, |M.drift w i| ≤ G * (1 + ‖w‖))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (w z : EthierKurtz.SDEState d) :
    ‖η • M.drift w + Real.sqrt η • mv M.σ z‖
      ≤ Real.sqrt η * ((d * G + Sσ M.σ) * ((1 + ‖w‖) * (1 + ‖z‖))) := by
  have hs0 : 0 ≤ Real.sqrt η := Real.sqrt_nonneg _
  have hηs : η ≤ Real.sqrt η := by
    rw [Real.le_sqrt hη.le hη.le]; nlinarith
  have h1 := drift_norm M G hG w
  have h2 := mv_norm_le M.σ z
  have hS := Sσ_nonneg M.σ
  have hw := norm_nonneg w
  have hz := norm_nonneg z
  have hdG : 0 ≤ (d : ℝ) * G := by positivity
  calc ‖η • M.drift w + Real.sqrt η • mv M.σ z‖
      ≤ ‖η • M.drift w‖ + ‖Real.sqrt η • mv M.σ z‖ := norm_add_le _ _
    _ = η * ‖M.drift w‖ + Real.sqrt η * ‖mv M.σ z‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hη,
          abs_of_nonneg hs0]
    _ ≤ Real.sqrt η * (d * G * (1 + ‖w‖)) + Real.sqrt η * (Sσ M.σ * ‖z‖) := by
        gcongr
    _ ≤ Real.sqrt η * ((d * G + Sσ M.σ) * ((1 + ‖w‖) * (1 + ‖z‖))) := by
        rw [← mul_add]
        gcongr
        nlinarith [mul_nonneg hdG hz, mul_nonneg hS hw, mul_nonneg (mul_nonneg hS hw) hz,
          mul_nonneg (mul_nonneg hdG hw) hz]

lemma gauss_mom :
    Integrable (fun z : EthierKurtz.SDEState d => (1 + ‖z‖) ^ 7) (stdGaussian (EthierKurtz.SDEState d)) := by
  have h7 : Integrable (fun z : EthierKurtz.SDEState d => ‖z‖ ^ 7)
      (stdGaussian (EthierKurtz.SDEState d)) :=
    (IsGaussian.memLp_id (stdGaussian (EthierKurtz.SDEState d)) ((7 : ℕ) : ℝ≥0∞)
      (by simp)).integrable_norm_pow (by norm_num)
  refine Integrable.mono' (((integrable_const 1).add h7).const_mul (2 ^ 7))
    (by fun_prop) (ae_of_all _ (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact one_add_pow_le _ (norm_nonneg _) 7

lemma mom (μt : Measure (EthierKurtz.SDEState d)) [IsProbabilityMeasure μt] (C7 : ℝ)
    (h7 : ∫⁻ x, ‖x‖ₑ ^ 7 ∂μt ≤ ENNReal.ofReal C7) :
    ∫⁻ w, ∫⁻ z, ENNReal.ofReal (((1 + ‖w‖) * (1 + ‖z‖)) ^ 7)
        ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt
      ≤ ENNReal.ofReal (2 ^ 7 * (1 + max C7 0) *
          ∫ z, (1 + ‖z‖) ^ 7 ∂(stdGaussian (EthierKurtz.SDEState d))) := by
  set Bγ := ∫ z, (1 + ‖z‖) ^ 7 ∂(stdGaussian (EthierKurtz.SDEState d))
  have hB : ∫⁻ z, ENNReal.ofReal ((1 + ‖z‖) ^ 7) ∂(stdGaussian (EthierKurtz.SDEState d))
      = ENNReal.ofReal Bγ :=
    (ofReal_integral_eq_lintegral_ofReal gauss_mom
      (ae_of_all _ (fun z => by positivity))).symm
  have hB0 : 0 ≤ Bγ := integral_nonneg (fun z => by positivity)
  have inner : ∀ w : EthierKurtz.SDEState d,
      ∫⁻ z, ENNReal.ofReal (((1 + ‖w‖) * (1 + ‖z‖)) ^ 7) ∂(stdGaussian (EthierKurtz.SDEState d))
        = ENNReal.ofReal ((1 + ‖w‖) ^ 7) * ENNReal.ofReal Bγ := by
    intro w
    simp_rw [mul_pow, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1 + ‖w‖) ^ 7)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hB]
  simp_rw [inner]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hW : ∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ 7) ∂μt ≤ ENNReal.ofReal (2 ^ 7 * (1 + max C7 0)) := by
    have hpt : ∀ w : EthierKurtz.SDEState d, ENNReal.ofReal ((1 + ‖w‖) ^ 7)
        ≤ ENNReal.ofReal (2 ^ 7) * (1 + ‖w‖ₑ ^ 7) := by
      intro w
      have := one_add_pow_le _ (norm_nonneg w) 7
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (by positivity),
        ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal this
    calc ∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ 7) ∂μt
        ≤ ∫⁻ w, ENNReal.ofReal (2 ^ 7) * (1 + ‖w‖ₑ ^ 7) ∂μt := lintegral_mono hpt
      _ = ENNReal.ofReal (2 ^ 7) * (1 + ∫⁻ w, ‖w‖ₑ ^ 7 ∂μt) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left measurable_const]
          simp
      _ ≤ ENNReal.ofReal (2 ^ 7) * (1 + ENNReal.ofReal (max C7 0)) := by
          gcongr
          exact h7.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal (2 ^ 7 * (1 + max C7 0)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add zero_le_one (le_max_right _ _),
            ENNReal.ofReal_one]
  calc (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ 7) ∂μt) * ENNReal.ofReal Bγ
      ≤ ENNReal.ofReal (2 ^ 7 * (1 + max C7 0)) * ENNReal.ofReal Bγ := by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

end EMErrClaimsAux

open GPhNGIDiffusion.EMError EMErrClaimsAux in
theorem solution {d : ℕ} (M : Model d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hP : IsTransitionFunction M.drift M.σ P)
    (μ : Measure (EthierKurtz.SDEState d)) (hμ : IsInvariantMeasure P μ) :
    let δ : ℝ → EthierKurtz.SDEState d → EthierKurtz.SDEState d → EthierKurtz.SDEState d :=
      fun η w z => η • M.drift w + Real.sqrt η • mv M.σ z
    let J : (EthierKurtz.SDEState d → ℝ) → EthierKurtz.SDEState d → EthierKurtz.SDEState d → ℝ :=
      fun h w u => ∫ r in (0 : ℝ)..1, ∫ r' in (0 : ℝ)..1,
        r * ∑ i, ∑ j, u i * u j *
          (partial2 (steinSolution P μ h) i j (w + (r' * r) • u)
            - partial2 (steinSolution P μ h) i j w)
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      (∀ ς : ℝ, 0 < ς → ς < 1 → ∃ Cς : ℝ, 0 < Cς ∧
        ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ μt : Measure (EthierKurtz.SDEState d),
          IsEMInvariant M.drift M.σ η μt → ∀ h : EthierKurtz.SDEState d → ℝ, IsLip1Zero h →
            ∫⁻ w, ∫⁻ z, (if ‖δ η w z‖ < 1 then ENNReal.ofReal |J h w (δ η w z)| else 0)
                ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt ≤
              ENNReal.ofReal (Cς * η ^ ((3 - ς) / 2))) ∧
      (∃ C : ℝ, 0 < C ∧
        ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ μt : Measure (EthierKurtz.SDEState d),
          IsEMInvariant M.drift M.σ η μt → ∀ h : EthierKurtz.SDEState d → ℝ, IsLip1Zero h →
            ∫⁻ w, ∫⁻ z, (if 1 ≤ ‖δ η w z‖ then ENNReal.ofReal |J h w (δ η w z)| else 0)
                ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt ≤
              ENNReal.ofReal (C * η ^ (3 / 2 : ℝ))) := by
  intro δ J
  obtain ⟨η₁0, hη₁0, huniq0, hmom⟩ := proposition_2_1_unique_moments M
  obtain ⟨ηL, hηL, C7, hC7'⟩ := hmom 7 (by norm_num)
  set η₁ : ℝ := min η₁0 ηL
  have hη₁ : 0 < η₁ := lt_min hη₁0 hηL
  have hC7 : ∀ η : ℝ, 0 < η → η ≤ η₁ → ∀ μt : Measure (EthierKurtz.SDEState d),
      IsEMInvariant M.drift M.σ η μt → ∫⁻ x, ‖x‖ₑ ^ 7 ∂μt ≤ ENNReal.ofReal C7 :=
    fun η h hl => hC7' η h (hl.trans (min_le_right _ _))
  obtain ⟨⟨C2, hC2, hstein⟩, hHolall⟩ := lemma_2_2 M P hP μ hμ
  obtain ⟨G, hG0, hG⟩ := drift_bound M
  set M0 : ℝ := (d : ℝ) * G + Sσ M.σ with hM0def
  have hM0 : 0 ≤ M0 := add_nonneg (by positivity) (Sσ_nonneg M.σ)
  set Mom : ℝ := 2 ^ 7 * (1 + max C7 0) *
    ∫ z, (1 + ‖z‖) ^ 7 ∂(stdGaussian (EthierKurtz.SDEState d)) with hMomdef
  have hMom : 0 ≤ Mom := mul_nonneg (by positivity) (integral_nonneg (fun z => by positivity))
  have hη0 : 0 < min η₁ (1 / 2) := lt_min hη₁ (by norm_num)
  have hη0' : min η₁ (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  -- common facts for a given step and stationary law
  have common : ∀ η : ℝ, 0 < η → η ≤ min η₁ (1 / 2) → ∀ μt, IsEMInvariant M.drift M.σ η μt →
      η ≤ 1 ∧ ∫⁻ w, ∫⁻ z, ENNReal.ofReal (((1 + ‖w‖) * (1 + ‖z‖)) ^ 7)
        ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt ≤ ENNReal.ofReal Mom := by
    intro η hη hηle μt hμt
    haveI := hμt.1
    refine ⟨hηle.trans ((min_le_right _ _).trans (by norm_num)), ?_⟩
    exact mom μt C7 (hC7 η hη (hηle.trans (min_le_left _ _)) μt hμt)
  refine ⟨min η₁ (1 / 2), hη0, hη0', fun ς hς0 hς1 => ?_, ?_⟩
  · obtain ⟨Cς, hCς, hHol⟩ := hHolall ς hς0 hς1
    set KA : ℝ := d * d * Cς * (1 + M0 ^ 3) with hKA
    have hKA0 : 0 ≤ KA := by positivity
    refine ⟨KA * Mom + 1, by positivity, fun η hη hηle μt hμt h hh => ?_⟩
    obtain ⟨hη1, hmomt⟩ := common η hη hηle μt hμt
    have hpt : ∀ w z, (if ‖δ η w z‖ < 1 then ENNReal.ofReal |J h w (δ η w z)| else 0)
        ≤ ENNReal.ofReal (KA * η ^ ((3 - ς) / 2)) *
          ENNReal.ofReal (((1 + ‖w‖) * (1 + ‖z‖)) ^ 7) := by
      intro w z
      split_ifs with hlt
      · rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hb := ptA (steinSolution P μ h) Cς ς hCς hς0 hς1
          (fun x y hxy i j => hHol h hh x y hxy i j) w (δ η w z) hlt η M0
          ((1 + ‖w‖) * (1 + ‖z‖)) hη hM0
          (one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg w])
            (by linarith [norm_nonneg z]))
          (le_mul_of_one_le_right (by positivity) (by linarith [norm_nonneg z]))
          (delta_bound M G hG0 hG η hη hη1 w z)
        refine le_trans hb (le_of_eq ?_)
        rw [hKA]
      · exact zero_le
    calc _ ≤ ∫⁻ w, ∫⁻ z, ENNReal.ofReal (KA * η ^ ((3 - ς) / 2)) *
            ENNReal.ofReal (((1 + ‖w‖) * (1 + ‖z‖)) ^ 7)
            ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt :=
          lintegral_mono (fun w => lintegral_mono (fun z => hpt w z))
      _ = ENNReal.ofReal (KA * η ^ ((3 - ς) / 2)) * ∫⁻ w, ∫⁻ z,
            ENNReal.ofReal (((1 + ‖w‖) * (1 + ‖z‖)) ^ 7)
            ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt := by
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (KA * η ^ ((3 - ς) / 2)) * ENNReal.ofReal Mom := by gcongr
      _ = ENNReal.ofReal (KA * Mom * η ^ ((3 - ς) / 2)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
      _ ≤ ENNReal.ofReal ((KA * Mom + 1) * η ^ ((3 - ς) / 2)) := by
          apply ENNReal.ofReal_le_ofReal
          have : 0 ≤ η ^ ((3 - ς) / 2) := by positivity
          nlinarith
  · set KB : ℝ := 2 * d * d * C2 * M0 ^ 3 * (1 + (1 + M0) ^ 3) with hKB
    have hKB0 : 0 ≤ KB := by positivity
    refine ⟨KB * Mom + 1, by positivity, fun η hη hηle μt hμt h hh => ?_⟩
    obtain ⟨hη1, hmomt⟩ := common η hη hηle μt hμt
    obtain ⟨-, -, hbds⟩ := hstein h hh
    have hpt : ∀ w z, (if 1 ≤ ‖δ η w z‖ then ENNReal.ofReal |J h w (δ η w z)| else 0)
        ≤ ENNReal.ofReal (KB * η ^ (3 / 2 : ℝ)) *
          ENNReal.ofReal (((1 + ‖w‖) * (1 + ‖z‖)) ^ 7) := by
      intro w z
      split_ifs with hge
      · rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hb := ptB (steinSolution P μ h) C2 hC2 (fun x i j => (hbds x i j).2.2)
          w (δ η w z) hge η M0 ((1 + ‖w‖) * (1 + ‖z‖)) hη hη1 hM0
          (one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg w])
            (by linarith [norm_nonneg z]))
          (le_mul_of_one_le_right (by positivity) (by linarith [norm_nonneg z]))
          (delta_bound M G hG0 hG η hη hη1 w z)
        refine le_trans hb (le_of_eq ?_)
        rw [hKB]
      · exact zero_le
    calc _ ≤ ∫⁻ w, ∫⁻ z, ENNReal.ofReal (KB * η ^ (3 / 2 : ℝ)) *
            ENNReal.ofReal (((1 + ‖w‖) * (1 + ‖z‖)) ^ 7)
            ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt :=
          lintegral_mono (fun w => lintegral_mono (fun z => hpt w z))
      _ = ENNReal.ofReal (KB * η ^ (3 / 2 : ℝ)) * ∫⁻ w, ∫⁻ z,
            ENNReal.ofReal (((1 + ‖w‖) * (1 + ‖z‖)) ^ 7)
            ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt := by
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (KB * η ^ (3 / 2 : ℝ)) * ENNReal.ofReal Mom := by gcongr
      _ = ENNReal.ofReal (KB * Mom * η ^ (3 / 2 : ℝ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
      _ ≤ ENNReal.ofReal ((KB * Mom + 1) * η ^ (3 / 2 : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          have : 0 ≤ η ^ (3 / 2 : ℝ) := by positivity
          nlinarith
