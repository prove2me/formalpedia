-- Prove2me | solution 1 for CohenLeeSongLP.StochCentralPath.potential_expected_decrease
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T05:14:02.863301+00:00
-- url     : https://prove2.me/submissions/1741ec65-6975-4bad-81b0-f15949e2729d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_Main
import Theorems.Thm_CohenLeeSongLP_StochCentralPath_mu_new_bounds
import Theorems.Thm_CohenLeeSongLP_StochCentralPath_potential_basic_properties
import Theorems.Thm_CohenLeeSongLP_StochCentralPath_success_probability

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace CohenLeeSongLP.StochCentralPath.L413

lemma one_lt_log {n : ℕ} (hn : 10 ≤ n) : 1 < Real.log n := by
  have h10 : (10:ℝ) ≤ n := by exact_mod_cast hn
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log n := Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

lemma sum_mul_div_norm2 {n : ℕ} (g : Fin n → ℝ) :
    ∑ i, g i * (g i / norm2 g) = norm2 g := by
  unfold norm2
  set G := Real.sqrt (∑ i, g i ^ 2) with hG
  have hsq : G ^ 2 = ∑ i, g i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases h0 : G = 0
  · rw [h0]; simp
  · have : ∑ i, g i * (g i / G) = (∑ i, g i ^ 2) / G := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← hsq]; field_simp

lemma sum_sq_div_norm2_le {n : ℕ} (g : Fin n → ℝ) :
    ∑ i, (g i / norm2 g) ^ 2 ≤ 1 := by
  unfold norm2
  set G := Real.sqrt (∑ i, g i ^ 2) with hG
  have hsq : G ^ 2 = ∑ i, g i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases h0 : G = 0
  · rw [h0]; simp
  · have : ∑ i, (g i / G) ^ 2 = (∑ i, g i ^ 2) / G ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← hsq, div_self (pow_ne_zero 2 h0)]

lemma abs_sum_mul_le {n : ℕ} (g w : Fin n → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∑ i, w i ^ 2 ≤ W ^ 2) : |∑ i, g i * w i| ≤ norm2 g * W := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g w
  have h1 : (∑ i, g i * w i) ^ 2 ≤ (∑ i, g i ^ 2) * W ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_left hw (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have h2 := Real.abs_le_sqrt h1
  rwa [Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _), Real.sqrt_sq hW] at h2

/-- The final real inequality of the proof of Lemma 4.13. -/
lemma final_ineq {n : ℕ} (hn : 10 ≤ n) (ε k Φ G M : ℝ) (hε : 0 < ε)
    (hεle : ε ≤ 1 / (40000 * Real.log n)) (hk : 40000000 * ε * Real.sqrt n * Real.log n ^ 2 ≤ k)
    (hΦn : (n : ℝ) ≤ Φ) (hG0 : 0 ≤ G) (hG : lam n / Real.sqrt n * (Φ - n) ≤ G)
    (hM : M ≤ lam n * Real.sqrt n + G)
    (S1 S2 Sh : ℝ) (hS1 : S1 ≤ -(ε / 2) * G + 0.02 * ε * G)
    (hS2 : S2 ≤ 72 * ε ^ 2 / k * Sh + lam n * M * (ε ^ 2 / 2 + 0.0008 * ε ^ 2))
    (hSh : Sh = lam n ^ 2 * Φ) :
    Φ + S1 + 2 * S2 ≤ Φ - lam n * ε / (15 * Real.sqrt n) * (Φ - 10 * n) := by
  have hL := one_lt_log hn
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
  have hlam : lam n = 40 * Real.log n := rfl
  have hlampos : 0 < lam n := by rw [hlam]; linarith
  have hle : lam n * ε ≤ 1 / 1000 := by
    rw [hlam]
    have : ε * (40000 * Real.log n) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hεle; linarith
    nlinarith
  have hkpos : 0 < k := lt_of_lt_of_le (by positivity) hk
  -- the variance term
  have hV : 72 * ε ^ 2 / k * Sh ≤ 0.00288 * (ε / Real.sqrt n) * Φ := by
    rw [hSh, div_mul_eq_mul_div, div_le_iff₀ hkpos]
    have hΦ0 : 0 ≤ Φ := by linarith
    have e1 : 72 * ε ^ 2 * (lam n ^ 2 * Φ) = 72 * 1600 * (ε * Real.log n ^ 2) * ε * Φ := by
      rw [hlam]; ring
    have e2 : 0.00288 * (ε / Real.sqrt n) * Φ * (40000000 * ε * Real.sqrt n * Real.log n ^ 2)
        = 72 * 1600 * (ε * Real.log n ^ 2) * ε * Φ := by
      field_simp; ring
    calc 72 * ε ^ 2 * (lam n ^ 2 * Φ) = 0.00288 * (ε / Real.sqrt n) * Φ *
          (40000000 * ε * Real.sqrt n * Real.log n ^ 2) := by rw [e1, e2]
      _ ≤ 0.00288 * (ε / Real.sqrt n) * Φ * k :=
          mul_le_mul_of_nonneg_left hk (by positivity)
  -- the Hessian term
  have hH : lam n * M * (ε ^ 2 / 2 + 0.0008 * ε ^ 2) ≤
      0.0005008 * (ε / Real.sqrt n) * lam n * n + 0.0005008 * ε * G := by
    have hM' : lam n * M ≤ lam n * (lam n * Real.sqrt n + G) :=
      mul_le_mul_of_nonneg_left hM hlampos.le
    have e : ε ^ 2 / 2 + 0.0008 * ε ^ 2 = 0.5008 * ε ^ 2 := by ring
    rw [e]
    have h1 : lam n * M * (0.5008 * ε ^ 2) ≤ lam n * (lam n * Real.sqrt n + G) * (0.5008 * ε ^ 2) :=
      mul_le_mul_of_nonneg_right hM' (by positivity)
    have e2 : lam n * (lam n * Real.sqrt n + G) * (0.5008 * ε ^ 2) =
        0.5008 * (lam n * ε) * (ε / Real.sqrt n) * lam n * n + 0.5008 * (lam n * ε) * ε * G := by
      have e3 : 0.5008 * (lam n * ε) * (ε / Real.sqrt n) * lam n * (Real.sqrt n * Real.sqrt n) +
          0.5008 * (lam n * ε) * ε * G = lam n * (lam n * Real.sqrt n + G) * (0.5008 * ε ^ 2) := by
        field_simp
      rw [hsn] at e3; exact e3.symm
    have h3 : 0.5008 * (lam n * ε) * (ε / Real.sqrt n) * lam n * n ≤
        0.5008 * (1 / 1000) * (ε / Real.sqrt n) * lam n * n := by
      have : 0 ≤ (ε / Real.sqrt n) * lam n * n := by positivity
      nlinarith
    have h4 : 0.5008 * (lam n * ε) * ε * G ≤ 0.5008 * (1 / 1000) * ε * G := by
      have : 0 ≤ ε * G := by positivity
      nlinarith
    linarith
  -- the gradient term, via Lemma 4.12 part 2
  have hGK : (ε / Real.sqrt n) * lam n * (Φ - n) ≤ ε * G := by
    have := mul_le_mul_of_nonneg_left hG hε.le
    calc (ε / Real.sqrt n) * lam n * (Φ - n) = ε * (lam n / Real.sqrt n * (Φ - n)) := by ring
      _ ≤ ε * G := this
  set K := ε / Real.sqrt n with hK
  have hKpos : 0 < K := by positivity
  have hT : lam n * ε / (15 * Real.sqrt n) * (Φ - 10 * n) = K * lam n * (Φ - 10 * n) / 15 := by
    rw [hK]; field_simp
  rw [hT]
  have hu : 0 ≤ Φ - n := by linarith
  have p1 : 0 ≤ K * (lam n - 1) * (Φ - n) := by
    have : 0 ≤ lam n - 1 := by rw [hlam]; linarith
    positivity
  have p2 : 0 ≤ K * (lam n - 1) * n := by
    have : 0 ≤ lam n - 1 := by rw [hlam]; linarith
    positivity
  have p3 : 0 ≤ K * n := by positivity
  have p4 : 0 ≤ K * (Φ - n) := by positivity
  nlinarith

lemma sq_sum_le {a b : ℝ} : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]

lemma w_bound {n : ℕ} (b e μ : Fin n → ℝ) (t ε q : ℝ) (ht : 0 < t) (hε : 0 < ε)
    (hq0 : 0.99999 ≤ q) (hq1 : q ≤ 1) (hμ : ∀ i, 0.9 * t ≤ μ i ∧ μ i ≤ 1.1 * t)
    (hb : ∑ i, b i ^ 2 ≤ (0.01 * ε * t) ^ 2) (he : ∑ i, e i ^ 2 ≤ (ε / 4000) ^ 2) :
    ∑ i, ((b i + μ i * e i) / (q * t)) ^ 2 ≤ (0.02 * ε) ^ 2 := by
  have ht' : 0 < q * t := by nlinarith
  have hterm : ∀ i, (q * t) ^ 2 * ((b i + μ i * e i) / (q * t)) ^ 2 ≤
      2 * b i ^ 2 + 2.42 * t ^ 2 * e i ^ 2 := by
    intro i
    have e1 : (q * t) ^ 2 * ((b i + μ i * e i) / (q * t)) ^ 2 = (b i + μ i * e i) ^ 2 := by
      field_simp
    rw [e1]
    have hμ2 : μ i ^ 2 ≤ 1.21 * t ^ 2 := by nlinarith [(hμ i).1, (hμ i).2]
    have h2 := sq_sum_le (a := b i) (b := μ i * e i)
    have h3 : (μ i * e i) ^ 2 ≤ 1.21 * t ^ 2 * e i ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right hμ2 (sq_nonneg _)
    linarith
  set W := ∑ i, ((b i + μ i * e i) / (q * t)) ^ 2 with hW
  have hsum : (q * t) ^ 2 * W ≤ 2 * ∑ i, b i ^ 2 + 2.42 * t ^ 2 * ∑ i, e i ^ 2 := by
    rw [hW, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hterm i
  have ht'2 : 0.99998 * t ^ 2 ≤ (q * t) ^ 2 := by
    have hq2 : 0.99998 ≤ q ^ 2 := by nlinarith
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hq2 (sq_nonneg t)
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h0 := mul_le_mul_of_nonneg_right ht'2 hW0
  have h1 : t ^ 2 * (0.99998 * W) ≤ t ^ 2 * (0.00020016 * ε ^ 2) := by
    have e2 : 2 * (0.01 * ε * t) ^ 2 + 2.42 * t ^ 2 * (ε / 4000) ^ 2 =
        t ^ 2 * (0.0002 * ε ^ 2 + 2.42 / 16000000 * ε ^ 2) := by ring
    have h3 : 2 * ∑ i, b i ^ 2 + 2.42 * t ^ 2 * ∑ i, e i ^ 2 ≤
        2 * (0.01 * ε * t) ^ 2 + 2.42 * t ^ 2 * (ε / 4000) ^ 2 := by
      have := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ 2.42 * t ^ 2 by positivity)
      linarith
    have h4 : t ^ 2 * (0.0002 * ε ^ 2 + 2.42 / 16000000 * ε ^ 2) ≤ t ^ 2 * (0.00020016 * ε ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ε]) (sq_nonneg t)
    have e3 : 0.99998 * t ^ 2 * W = t ^ 2 * (0.99998 * W) := by ring
    linarith
  have h2 := le_of_mul_le_mul_left h1 (by positivity)
  nlinarith [sq_nonneg ε]

lemma sums_bound {n : ℕ} (g m w h s2 : Fin n → ℝ) (G M ε k lamv : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (hG : G = norm2 g) (hmean : ∀ i, m i = -(ε / 2) * (g i / G) + w i)
    (hw2 : ∑ i, w i ^ 2 ≤ (0.02 * ε) ^ 2) (hhnn : ∀ i, 0 ≤ h i) (hhM : ∀ i, h i ≤ lamv * M)
    (hlM : 0 ≤ lamv * M) (hs2b : ∀ i, s2 i ≤ 72 * ε ^ 2 / k + m i ^ 2) :
    ∑ i, g i * m i ≤ -(ε / 2) * G + 0.02 * ε * G ∧
    ∑ i, h i * s2 i ≤ 72 * ε ^ 2 / k * ∑ i, h i + lamv * M * (ε ^ 2 / 2 + 0.0008 * ε ^ 2) := by
  constructor
  · have e : ∑ i, g i * m i = -(ε / 2) * ∑ i, g i * (g i / G) + ∑ i, g i * w i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hmean i]; ring
    have h1 := sum_mul_div_norm2 g
    rw [← hG] at h1
    have hcs := abs_sum_mul_le g w (0.02 * ε) (by positivity) hw2
    rw [← hG] at hcs
    rw [e, h1]
    have := le_abs_self (∑ i, g i * w i)
    linarith
  · have hm2 : ∀ i, m i ^ 2 ≤ ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2 := by
      intro i
      rw [hmean i]
      have := sq_sum_le (a := -(ε / 2) * (g i / G)) (b := w i)
      have e : 2 * (-(ε / 2) * (g i / G)) ^ 2 = ε ^ 2 / 2 * (g i / G) ^ 2 := by ring
      linarith
    have step1 : ∑ i, h i * s2 i ≤ ∑ i, (72 * ε ^ 2 / k * h i +
        lamv * M * (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2)) := by
      apply Finset.sum_le_sum; intro i _
      have h1 : h i * s2 i ≤ h i * (72 * ε ^ 2 / k + (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith [hm2 i, hs2b i]) (hhnn i)
      have h2 : h i * (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2) ≤
          lamv * M * (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2) :=
        mul_le_mul_of_nonneg_right (hhM i) (by positivity)
      have e : h i * (72 * ε ^ 2 / k + (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2)) =
          72 * ε ^ 2 / k * h i + h i * (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2) := by ring
      linarith
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at step1
    have hg2 := sum_sq_div_norm2_le g
    rw [← hG] at hg2
    have h3 : ∑ i, (ε ^ 2 / 2 * (g i / G) ^ 2 + 2 * w i ^ 2) ≤ ε ^ 2 / 2 + 0.0008 * ε ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have := mul_le_mul_of_nonneg_left hg2 (show (0:ℝ) ≤ ε ^ 2 / 2 by positivity)
      nlinarith [hw2]
    have := mul_le_mul_of_nonneg_left h3 hlM
    linarith

/-- Lemma 4.13 from the bounds of Lemma 4.8, Lemma 4.12 and a bound on the conditioning bias,
for an abstract probability law `P` of the sample and an abstract `μ^new = Mn`. -/
lemma core {n : ℕ} (hn : 10 ≤ n) (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (Mn : (Fin n → ℝ) → Fin n → ℝ) (hMn : ∀ i, Continuous fun δ => Mn δ i)
    (μ δμ : Fin n → ℝ) (t ε εmp k : ℝ) (ht : 0 < t) (hε : 0 < ε)
    (hεle : ε ≤ 1 / (40000 * Real.log n)) (hεmp : 0 < εmp) (hεmp' : εmp ≤ 1 / 40000)
    (hk : 1000 * ε * Real.sqrt n * Real.log n ^ 2 / εmp ≤ k)
    (hμ : ∀ i, 0.9 * t ≤ μ i ∧ μ i ≤ 1.1 * t)
    (hδμ : ∀ i, δμ i = ((1 - ε / (3 * Real.sqrt n)) * t / t - 1) * μ i -
        ε / 2 * ((1 - ε / (3 * Real.sqrt n)) * t) *
        (potentialGrad (lam n) (fun l => μ l / t - 1) i /
          norm2 (potentialGrad (lam n) (fun l => μ l / t - 1))))
    (hsup : ∀ᵐ δ ∂P, ∀ i, |(Mn δ i - μ i) / μ i| ≤ 0.021 / Real.log n)
    (B : ℝ) (hδbd : ∀ᵐ δ ∂P, ∀ i, |δ i| ≤ B)
    (he : norm2 (fun i => ∫ δ, (Mn δ i - μ i - δ i) / μ i ∂P) ≤ 10 * εmp * ε)
    (hvar : ∀ i, variance (fun δ => Mn δ i / μ i) P ≤ 50 * ε ^ 2 / k)
    (hb : ∑ i, (∫ δ, δ i ∂P - δμ i) ^ 2 ≤ (0.01 * ε * t) ^ 2) :
    ∫ δ, potential (lam n) (fun i => Mn δ i / ((1 - ε / (3 * Real.sqrt n)) * t) - 1) ∂P
      ≤ potential (lam n) (fun i => μ i / t - 1) -
        lam n * ε / (15 * Real.sqrt n) * (potential (lam n) (fun i => μ i / t - 1) - 10 * n) := by
  have hL := one_lt_log hn
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hsq3 : 3 ≤ Real.sqrt n := by
    rw [show (3:ℝ) = Real.sqrt 9 by
      rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : 0 < Real.sqrt n := by linarith
  have hεL : ε * Real.log n ≤ 1 / 40000 := by
    rw [le_div_iff₀ (by positivity)] at hεle; linarith
  have hε1 : ε ≤ 1 / 40000 := by nlinarith
  have hlam : lam n = 40 * Real.log n := rfl
  have hlampos : 0 < lam n := by rw [hlam]; linarith
  set α := ε / (3 * Real.sqrt n) with hα
  have hα0 : 0 < α := by positivity
  have hαle : α ≤ ε / 9 := div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
  have hαL : α * Real.log n ≤ 1 / 360000 := by nlinarith
  have hq0 : 0.99999 ≤ 1 - α := by linarith
  have ht'0 : 0 < (1 - α) * t := by nlinarith
  set t' := (1 - α) * t with ht'
  set r : Fin n → ℝ := fun i => μ i / t - 1 with hr
  set g := potentialGrad (lam n) r with hg
  set G := norm2 g with hG
  have hμpos : ∀ i, 0 < μ i := fun i => by linarith [(hμ i).1]
  have hμt' : ∀ i, μ i / t' ≤ 1.1001 := fun i => by
    rw [div_le_iff₀ ht'0, ht']; nlinarith [(hμ i).2]
  have hμt'0 : ∀ i, 0 < μ i / t' := fun i => div_pos (hμpos i) ht'0
  obtain ⟨V, hV⟩ : ∃ V : Fin n → (Fin n → ℝ) → ℝ, V = fun i δ => Mn δ i / t' - 1 - r i :=
    ⟨_, rfl⟩
  have hVcont : ∀ i, Continuous (V i) := fun i => by
    rw [hV]; exact (((hMn i).div_const _).sub continuous_const).sub continuous_const
  -- a.e. size of the step
  have hVbd : ∀ᵐ δ ∂P, ∀ i, |V i δ| ≤ 1 / lam n := by
    filter_upwards [hsup] with δ hδ i
    have e : V i δ = μ i / t' * ((Mn δ i - μ i) / μ i) + μ i / t' * α := by
      have := (hμpos i).ne'
      rw [hV, hr, ht']; field_simp; ring
    have h1 : |V i δ| ≤ μ i / t' * (0.021 / Real.log n + α) := by
      rw [e]
      calc |μ i / t' * ((Mn δ i - μ i) / μ i) + μ i / t' * α|
          ≤ |μ i / t' * ((Mn δ i - μ i) / μ i)| + |μ i / t' * α| := abs_add_le _ _
        _ = μ i / t' * |(Mn δ i - μ i) / μ i| + μ i / t' * α := by
            rw [abs_mul, abs_mul, abs_of_pos (hμt'0 i), abs_of_pos hα0]
        _ ≤ μ i / t' * (0.021 / Real.log n) + μ i / t' * α := by
            have := mul_le_mul_of_nonneg_left (hδ i) (hμt'0 i).le; linarith
        _ = μ i / t' * (0.021 / Real.log n + α) := by ring
    have h2 : μ i / t' * (0.021 / Real.log n + α) ≤ 1.1001 * (0.021 / Real.log n + α) :=
      mul_le_mul_of_nonneg_right (hμt' i) (by positivity)
    have h3 : 1.1001 * (0.021 / Real.log n + α) ≤ 1 / lam n := by
      rw [hlam]
      have e2 : 1.1001 * (0.021 / Real.log n + α) = 1.1001 * (0.021 + α * Real.log n) / Real.log n := by
        field_simp
      have e3 : (1:ℝ) / (40 * Real.log n) = (1 / 40) / Real.log n := by
        rw [div_div]
      rw [e2, e3]
      apply div_le_div_of_nonneg_right _ (by linarith)
      nlinarith
    linarith
  have hMnbd : ∀ᵐ δ ∂P, ∀ i, |Mn δ i| ≤ 3 * t := by
    filter_upwards [hsup] with δ hδ i
    have e : Mn δ i = μ i * ((Mn δ i - μ i) / μ i) + μ i := by
      field_simp [(hμpos i).ne']; ring
    have h0 : 0.021 / Real.log n ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    rw [e]
    calc |μ i * ((Mn δ i - μ i) / μ i) + μ i| ≤ |μ i * ((Mn δ i - μ i) / μ i)| + |μ i| :=
          abs_add_le _ _
      _ = μ i * |(Mn δ i - μ i) / μ i| + μ i := by
          rw [abs_mul, abs_of_pos (hμpos i)]
      _ ≤ μ i * 1 + μ i := by
          have := mul_le_mul_of_nonneg_left ((hδ i).trans h0) (hμpos i).le; linarith
      _ ≤ 3 * t := by linarith [(hμ i).2]
  -- integrability
  have hMnI : ∀ i, Integrable (fun δ => Mn δ i) P := fun i =>
    Integrable.of_bound (hMn i).aestronglyMeasurable (3 * t)
      (by filter_upwards [hMnbd] with δ hδ; rw [Real.norm_eq_abs]; exact hδ i)
  have hδI : ∀ i, Integrable (fun δ : Fin n → ℝ => δ i) P := fun i =>
    Integrable.of_bound (continuous_apply i).aestronglyMeasurable B
      (by filter_upwards [hδbd] with δ hδ; rw [Real.norm_eq_abs]; exact hδ i)
  have hVI : ∀ i, Integrable (V i) P := fun i =>
    Integrable.of_bound (hVcont i).aestronglyMeasurable (1 / lam n)
      (by filter_upwards [hVbd] with δ hδ; rw [Real.norm_eq_abs]; exact hδ i)
  have hV2I : ∀ i, Integrable (fun δ => V i δ ^ 2) P := fun i =>
    Integrable.of_bound ((hVcont i).pow 2).aestronglyMeasurable ((1 / lam n) ^ 2)
      (by
        filter_upwards [hVbd] with δ hδ
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hδ i) 2)
  have hVL2 : ∀ i, MemLp (V i) 2 P := fun i =>
    MemLp.of_bound (hVcont i).aestronglyMeasurable (1 / lam n)
      (by filter_upwards [hVbd] with δ hδ; rw [Real.norm_eq_abs]; exact hδ i)
  -- Lemma 4.12
  obtain ⟨h412a, h412b, h412c⟩ := potential_basic_properties hn (lam n) hlampos r
  set h : Fin n → ℝ := fun i => lam n ^ 2 * Real.cosh (lam n * r i) with hh
  set Φ0 := potential (lam n) r with hΦ0
  -- the pointwise second-order bound
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℝ) → ℝ, F = fun δ =>
      Φ0 + ∑ i, g i * V i δ + 2 * ∑ i, h i * V i δ ^ 2 := ⟨_, rfl⟩
  have hpt : ∀ᵐ δ ∂P,
      potential (lam n) (fun i => Mn δ i / t' - 1) ≤ F δ := by
    filter_upwards [hVbd] with δ hδ
    have e : (fun i => Mn δ i / t' - 1) = (fun i => r i + (fun j => V j δ) i) := by
      funext i; rw [hV]; ring
    rw [e, hF]
    exact h412a (fun j => V j δ) hδ
  have hFI : Integrable F P := by
    rw [hF]
    refine ((integrable_const Φ0).add ?_).add (Integrable.const_mul ?_ 2)
    · exact integrable_finsetSum _ fun i _ => (hVI i).const_mul (g i)
    · exact integrable_finsetSum _ fun i _ => (hV2I i).const_mul (h i)
  have hΦnew_cont : Continuous fun δ => potential (lam n) (fun i => Mn δ i / t' - 1) := by
    unfold potential
    exact continuous_finset_sum _ fun i _ =>
      Real.continuous_cosh.comp (continuous_const.mul (((hMn i).div_const _).sub continuous_const))
  have hmono : ∫ δ, potential (lam n) (fun i => Mn δ i / t' - 1) ∂P ≤ ∫ δ, F δ ∂P := by
    refine integral_mono_ae ?_ hFI hpt
    refine Integrable.mono' hFI hΦnew_cont.aestronglyMeasurable ?_
    filter_upwards [hpt] with δ hδ
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hδ
    · unfold potential; exact Finset.sum_nonneg fun i _ => (Real.cosh_pos _).le
  set m : Fin n → ℝ := fun i => ∫ δ, V i δ ∂P with hm
  set s2 : Fin n → ℝ := fun i => ∫ δ, V i δ ^ 2 ∂P with hs2
  have hFint : ∫ δ, F δ ∂P = Φ0 + ∑ i, g i * m i + 2 * ∑ i, h i * s2 i := by
    rw [hF, integral_add, integral_add, integral_const, integral_const_mul,
      integral_finset_sum, integral_finset_sum]
    · simp only [probReal_univ, one_smul, hm, hs2, integral_const_mul]
    · exact fun i _ => (hV2I i).const_mul (h i)
    · exact fun i _ => (hVI i).const_mul (g i)
    · exact integrable_const _
    · exact integrable_finsetSum _ fun i _ => (hVI i).const_mul (g i)
    · exact (integrable_const _).add (integrable_finsetSum _ fun i _ => (hVI i).const_mul (g i))
    · exact Integrable.const_mul (integrable_finsetSum _ fun i _ => (hV2I i).const_mul (h i)) 2
  -- the mean of the step
  set e : Fin n → ℝ := fun i => ∫ δ, (Mn δ i - μ i - δ i) / μ i ∂P with he_def
  set b : Fin n → ℝ := fun i => ∫ δ, δ i ∂P - δμ i with hb_def
  set w : Fin n → ℝ := fun i => (b i + μ i * e i) / t' with hw_def
  have hmean : ∀ i, m i = -(ε / 2) * (g i / G) + w i := by
    intro i
    have h1 : m i = (∫ δ, Mn δ i ∂P) / t' - 1 - r i := by
      simp only [hm, hV]
      rw [integral_sub, integral_sub, integral_div, integral_const, integral_const]
      · simp
      · exact (hMnI i).div_const _
      · exact integrable_const _
      · exact ((hMnI i).div_const _).sub (integrable_const _)
      · exact integrable_const _
    have h2 : e i = ((∫ δ, Mn δ i ∂P) - μ i - ∫ δ, δ i ∂P) / μ i := by
      simp only [he_def]
      rw [integral_div, integral_sub, integral_sub, integral_const]
      · simp
      · exact hMnI i
      · exact integrable_const _
      · exact (hMnI i).sub (integrable_const _)
      · exact hδI i
    have h3 : ∫ δ, Mn δ i ∂P = μ i * e i + μ i + ∫ δ, δ i ∂P := by
      rw [h2]; field_simp [(hμpos i).ne']; ring
    have h4 : ∫ δ, δ i ∂P = b i + δμ i := by simp only [hb_def]; ring
    rw [h1, h3, h4, hδμ i]
    simp only [hw_def, hr]
    field_simp
    ring
  -- second moments
  have hkpos : 0 < k := lt_of_lt_of_le (by positivity) hk
  have hk' : 40000000 * ε * Real.sqrt n * Real.log n ^ 2 ≤ k := by
    refine le_trans ?_ hk
    rw [le_div_iff₀ hεmp]
    have : 0 ≤ ε * Real.sqrt n * Real.log n ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hεmp' this
    linarith
  have hs2b : ∀ i, s2 i ≤ 72 * ε ^ 2 / k + m i ^ 2 := by
    intro i
    have e : V i = fun δ => μ i / t' * (Mn δ i / μ i) + (-1 - r i) := by
      have := (hμpos i).ne'
      rw [hV]; funext δ; field_simp; ring
    have hvarV : variance (V i) P ≤ 1.1001 ^ 2 * (50 * ε ^ 2 / k) := by
      have hXm : AEStronglyMeasurable (fun δ => μ i / t' * (Mn δ i / μ i)) P :=
        (((hMn i).div_const _).const_mul _).aestronglyMeasurable
      rw [e, variance_add_const hXm, variance_const_mul]
      exact mul_le_mul (pow_le_pow_left₀ (hμt'0 i).le (hμt' i) 2) (hvar i)
        (variance_nonneg _ _) (by positivity)
    have e1 : s2 i = variance (V i) P + m i ^ 2 := by
      rw [variance_eq_sub (hVL2 i)]
      simp only [hs2, hm, Pi.pow_apply]
      ring
    have h72 : 1.1001 ^ 2 * (50 * ε ^ 2 / k) ≤ 72 * ε ^ 2 / k := by
      rw [← mul_div_assoc, ← mul_assoc]
      apply div_le_div_of_nonneg_right _ hkpos.le
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg ε)
    linarith
  have hb' : ∑ i, b i ^ 2 ≤ (0.01 * ε * t) ^ 2 := hb
  have he2 : ∑ i, e i ^ 2 ≤ (ε / 4000) ^ 2 := by
    have h1 : ∑ i, e i ^ 2 = (norm2 e) ^ 2 := by
      unfold norm2; rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    rw [h1]
    have h2 : 10 * εmp * ε ≤ ε / 4000 := by
      have := mul_le_mul_of_nonneg_right hεmp' hε.le; linarith
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (he.trans h2) 2
  have hw2 : ∑ i, w i ^ 2 ≤ (0.02 * ε) ^ 2 :=
    w_bound b e μ t ε (1 - α) ht hε hq0 (by linarith) hμ hb' he2
  have hhnn : ∀ i, 0 ≤ h i := fun i => (mul_pos (by positivity) (Real.cosh_pos _)).le
  set M := Real.sqrt (∑ i, lam n ^ 2 * Real.cosh (lam n * r i) ^ 2) with hM
  have hhM : ∀ i, h i ≤ lam n * M := by
    intro i
    have h1 : lam n * Real.cosh (lam n * r i) ≤ M := by
      have h2 : (lam n * Real.cosh (lam n * r i)) ^ 2 ≤
          ∑ j, lam n ^ 2 * Real.cosh (lam n * r j) ^ 2 := by
        rw [mul_pow]
        exact Finset.single_le_sum (f := fun j => lam n ^ 2 * Real.cosh (lam n * r j) ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ i)
      exact (le_abs_self _).trans (Real.abs_le_sqrt h2)
    calc h i = lam n * (lam n * Real.cosh (lam n * r i)) := by simp only [hh]; ring
      _ ≤ lam n * M := mul_le_mul_of_nonneg_left h1 hlampos.le
  have hlM : 0 ≤ lam n * M := mul_nonneg hlampos.le (Real.sqrt_nonneg _)
  obtain ⟨hS1, hS2⟩ := sums_bound g m w h s2 G M ε k (lam n) hε hkpos hG hmean hw2 hhnn hhM hlM hs2b
  have hSh : ∑ i, h i = lam n ^ 2 * Φ0 := by
    simp only [hh, hΦ0, potential, Finset.mul_sum]
  have hΦn : (n : ℝ) ≤ Φ0 := by
    simp only [hΦ0, potential]
    calc (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => Real.one_le_cosh _
  have h412b' : lam n / Real.sqrt n * (Φ0 - n) ≤ G := h412b
  have h412c' : M ≤ lam n * Real.sqrt n + G := h412c
  have hfin := final_ineq hn ε k Φ0 G M hε hεle hk' hΦn (Real.sqrt_nonneg _) h412b' h412c'
    (∑ i, g i * m i) (∑ i, h i * s2 i) (∑ i, h i) hS1 hS2 hSh
  calc ∫ δ, potential (lam n) (fun i => Mn δ i / t' - 1) ∂P ≤ ∫ δ, F δ ∂P := hmono
    _ = Φ0 + ∑ i, g i * m i + 2 * ∑ i, h i * s2 i := hFint
    _ ≤ _ := hfin

/-- `C M C = C` for `C = M⁻¹` (Mathlib's inverse is `0` on singular matrices). -/
lemma inv_mul_mul_inv {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : M⁻¹ * M * M⁻¹ = M⁻¹ := by
  by_cases h : IsUnit M.det
  · rw [Matrix.nonsing_inv_mul M h, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit M h]; simp

lemma proj_idem {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin d) (Fin d) ℝ)
    (hCt : C.transpose = C) (hCMC : C * (B * B.transpose) * C = C) :
    (B.transpose * C * B).transpose * (B.transpose * C * B) = B.transpose * C * B := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hCt]
  calc B.transpose * (C * B) * (B.transpose * C * B)
      = B.transpose * (C * (B * B.transpose) * C) * B := by simp only [Matrix.mul_assoc]
    _ = B.transpose * C * B := by rw [hCMC]

/-- Every entry of `P̄` is at most `1` in absolute value: `P̄ᵀ P̄ = P̄`. -/
lemma projBar_entry_le {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (xb sb : Fin n → ℝ)
    (hx : ∀ i, 0 < xb i) (hs : ∀ i, 0 < sb i) (i j : Fin n) :
    |projBar A xb sb j i| ≤ 1 := by
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin n) ℝ,
      D = Matrix.diagonal (fun i => Real.sqrt (xb i / sb i)) := ⟨_, rfl⟩
  have hDt : D.transpose = D := by rw [hD]; exact Matrix.diagonal_transpose _
  have hW : Matrix.diagonal (fun i => xb i / sb i) = D * D := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [Real.mul_self_sqrt (div_pos (hx i) (hs i)).le]
  have hP : projBar A xb sb = (A * D).transpose * ((A * D) * (A * D).transpose)⁻¹ * (A * D) := by
    unfold projBar
    rw [hW, ← hD, Matrix.transpose_mul, hDt]
    simp only [Matrix.mul_assoc]
  have hCt : (((A * D) * (A * D).transpose)⁻¹).transpose = ((A * D) * (A * D).transpose)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPP : (projBar A xb sb).transpose * projBar A xb sb = projBar A xb sb := by
    rw [hP]; exact proj_idem _ _ hCt (inv_mul_mul_inv _)
  obtain ⟨P, hPdef⟩ : ∃ P, P = projBar A xb sb := ⟨_, rfl⟩
  rw [← hPdef] at hPP ⊢
  have hcol : ∀ i, ∑ j, P j i ^ 2 = P i i := by
    intro i
    have := congrFun (congrFun hPP i) i
    rw [Matrix.mul_apply] at this
    simpa [Matrix.transpose_apply, sq] using this
  have hii : P i i ≤ 1 := by
    have h1 : P i i ^ 2 ≤ ∑ j, P j i ^ 2 :=
      Finset.single_le_sum (f := fun j => P j i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hcol i] at h1
    nlinarith [sq_nonneg (P i i)]
  have h2 : P j i ^ 2 ≤ 1 := by
    have : P j i ^ 2 ≤ ∑ k, P k i ^ 2 :=
      Finset.single_le_sum (f := fun k => P k i ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    rw [hcol i] at this; linarith
  have := Real.abs_le_sqrt h2
  rwa [Real.sqrt_one] at this

lemma stepX_add {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v u w : Fin n → ℝ) (j : Fin n) :
    stepX A x s v (u + w) j = stepX A x s v u j + stepX A x s v w j := by
  unfold stepX pMu
  have e : (fun l => (u + w) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      (fun l => u l / Real.sqrt (xbar x s v l * sbar x s v l)) +
      (fun l => w l / Real.sqrt (xbar x s v l * sbar x s v l)) := by
    funext l; simp [add_div]
  rw [e, Matrix.mulVec_add]
  simp only [Pi.add_apply]
  ring

lemma stepS_add {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v u w : Fin n → ℝ) (j : Fin n) :
    stepS A x s v (u + w) j = stepS A x s v u j + stepS A x s v w j := by
  unfold stepS pMu
  have e : (fun l => (u + w) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      (fun l => u l / Real.sqrt (xbar x s v l * sbar x s v l)) +
      (fun l => w l / Real.sqrt (xbar x s v l * sbar x s v l)) := by
    funext l; simp [add_div]
  rw [e, Matrix.mulVec_add]
  simp only [Pi.add_apply]
  ring

lemma pMu_single {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n)
    (a : ℝ) (j : Fin n) :
    pMu A x s v (Pi.single i a) j = projBar A (xbar x s v) (sbar x s v) j i *
      (a / Real.sqrt (xbar x s v i * sbar x s v i)) := by
  unfold pMu
  have e : (fun l => (Pi.single i a : Fin n → ℝ) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      Pi.single i (a / Real.sqrt (xbar x s v i * sbar x s v i)) := by
    funext l
    by_cases h : l = i
    · subst h; simp
    · simp [h]
  rw [e]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The effect of one coordinate of the sample on the normalised steps. -/
lemma single_step_bound {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ)
    (hxb : ∀ j, 0 < xbar x s v j) (hsb : ∀ j, 0 < sbar x s v j) (c : ℝ) (hc : 0 < c)
    (hcj : ∀ j, c ≤ xbar x s v j * sbar x s v j) (i : Fin n) (a : ℝ) (j : Fin n) :
    |stepS A x s v (Pi.single i a) j / sbar x s v j| ≤ |a| / c ∧
    |stepX A x s v (Pi.single i a) j / xbar x s v j| ≤ 2 * (|a| / c) := by
  set mi := xbar x s v i * sbar x s v i with hmi
  set mj := xbar x s v j * sbar x s v j with hmj
  have hmi0 : 0 < mi := mul_pos (hxb i) (hsb i)
  have hmj0 : 0 < mj := mul_pos (hxb j) (hsb j)
  have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hsi : Real.sqrt c ≤ Real.sqrt mi := Real.sqrt_le_sqrt (hcj i)
  have hsj : Real.sqrt c ≤ Real.sqrt mj := Real.sqrt_le_sqrt (hcj j)
  have hsc0 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hprod : c ≤ Real.sqrt mi * Real.sqrt mj := by
    rw [← hsc, sq]; exact mul_le_mul hsi hsj hsc0.le (Real.sqrt_nonneg _)
  have hP := projBar_entry_le A (xbar x s v) (sbar x s v) hxb hsb i j
  set p := pMu A x s v (Pi.single i a) j with hp
  have hpj : |p| ≤ |a| / Real.sqrt mi := by
    rw [hp, pMu_single, abs_mul, abs_div, abs_of_pos (Real.sqrt_pos.2 hmi0)]
    calc |projBar A (xbar x s v) (sbar x s v) j i| * (|a| / Real.sqrt mi)
        ≤ 1 * (|a| / Real.sqrt mi) := mul_le_mul_of_nonneg_right hP (by positivity)
      _ = |a| / Real.sqrt mi := one_mul _
  have hkey : |p / Real.sqrt mj| ≤ |a| / c := by
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 hmj0)]
    calc |p| / Real.sqrt mj ≤ (|a| / Real.sqrt mi) / Real.sqrt mj :=
          div_le_div_of_nonneg_right hpj (Real.sqrt_nonneg _)
      _ = |a| / (Real.sqrt mi * Real.sqrt mj) := by rw [div_div]
      _ ≤ |a| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hprod
  have eS : stepS A x s v (Pi.single i a) j / sbar x s v j = p / Real.sqrt mj := by
    unfold stepS
    rw [← hp]
    have := (hsb j).ne'
    rw [hmj]
    field_simp
  have eX : stepX A x s v (Pi.single i a) j / xbar x s v j =
      (Pi.single i a : Fin n → ℝ) j / mj - p / Real.sqrt mj := by
    unfold stepX
    rw [← hp]
    have := (hsb j).ne'
    have := (hxb j).ne'
    have := (Real.sqrt_pos.2 hmj0).ne'
    rw [hmj]
    field_simp
  refine ⟨by rw [eS]; exact hkey, ?_⟩
  rw [eX]
  have h1 : |(Pi.single i a : Fin n → ℝ) j / mj| ≤ |a| / c := by
    rw [abs_div, abs_of_pos hmj0]
    have ha : |(Pi.single i a : Fin n → ℝ) j| ≤ |a| := by
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    calc |(Pi.single i a : Fin n → ℝ) j| / mj ≤ |a| / mj := div_le_div_of_nonneg_right ha hmj0.le
      _ ≤ |a| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc (hcj j)
  calc |(Pi.single i a : Fin n → ℝ) j / mj - p / Real.sqrt mj|
      ≤ |(Pi.single i a : Fin n → ℝ) j / mj| + |p / Real.sqrt mj| := abs_sub _ _
    _ ≤ |a| / c + |a| / c := add_le_add h1 hkey
    _ = 2 * (|a| / c) := by ring



lemma sum_sq_div_norm2_le' {n : ℕ} (g : Fin n → ℝ) :
    ∑ i, (g i / norm2 g) ^ 2 ≤ 1 := by
  unfold norm2
  set G := Real.sqrt (∑ i, g i ^ 2) with hG
  have hsq : G ^ 2 = ∑ i, g i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases h0 : G = 0
  · rw [h0]; simp
  · have : ∑ i, (g i / G) ^ 2 = (∑ i, g i ^ 2) / G ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← hsq, div_self (pow_ne_zero 2 h0)]

lemma coordLaw_univ (p a : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) : coordLaw p a Set.univ = 1 := by
  simp only [coordLaw, Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_def,
    smul_eq_mul, mul_one]
  rw [← ENNReal.coe_add, ← Real.toNNReal_add hp0.le (by linarith)]
  simp

lemma coordLaw_isProb (p a : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (coordLaw p a) := ⟨coordLaw_univ p a hp0 hp1⟩

lemma integral_coordLaw (p a : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (f : ℝ → ℝ) :
    ∫ y, f y ∂(coordLaw p a) = p * f (a / p) + (1 - p) * f 0 := by
  unfold coordLaw
  rw [integral_add_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_dirac, integral_dirac]
  · simp [NNReal.smul_def, Real.coe_toNNReal _ hp0.le, Real.coe_toNNReal _ (by linarith : 0 ≤ 1 - p)]
  · exact (integrable_dirac enorm_lt_top).smul_measure_nnreal
  · exact (integrable_dirac enorm_lt_top).smul_measure_nnreal

lemma coordLaw_bad (p a : ℝ) (hp0 : 0 < p) : coordLaw p a {y | |a| / p < |y|} = 0 := by
  unfold coordLaw
  have hm : MeasurableSet {y : ℝ | |a| / p < |y|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hm,
    Measure.dirac_apply' _ hm]
  have h1 : a / p ∉ {y : ℝ | |a| / p < |y|} := by
    simp [abs_div, abs_of_pos hp0]
  have h2 : (0:ℝ) ∉ {y : ℝ | |a| / p < |y|} := by
    simp only [Set.mem_setOf_eq, abs_zero, not_lt]; positivity
  rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  simp

lemma sampleProb_pos {n : ℕ} (hn : 0 < n) (k : ℝ) (hk : 0 < k) (δμ : Fin n → ℝ) (i : Fin n) :
    0 < sampleProb k δμ i ∧ sampleProb k δμ i ≤ 1 := by
  unfold sampleProb
  refine ⟨lt_min one_pos ?_, min_le_left _ _⟩
  have : 0 ≤ δμ i ^ 2 / ∑ l, δμ l ^ 2 :=
    div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun l _ => sq_nonneg _)
  have : (0:ℝ) < 1 / (n : ℝ) := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  positivity

/-- Coordinate `i` of a product law is independent of the other coordinates. -/
lemma indep_update {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (H : Set (Fin n → ℝ)) (hH : MeasurableSet H) :
    ∫ δ, |δ i| * H.indicator 1 (Function.update δ i 0) ∂(Measure.pi μs) =
      (∫ δ, |δ i| ∂(Measure.pi μs)) *
        ∫ δ, H.indicator 1 (Function.update δ i 0) ∂(Measure.pi μs) := by
  have hI := iIndepFun_pi (μ := μs) (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hdisj : Disjoint ({i} : Finset (Fin n)) (Finset.univ.erase i) := by simp
  have h2 := hI.indepFun_finset {i} (Finset.univ.erase i) hdisj
    (fun j => measurable_id.comp (measurable_pi_apply j))
  set φ : (({i} : Finset (Fin n)) → ℝ) → ℝ := fun y => |y ⟨i, Finset.mem_singleton_self i⟩|
    with hφ
  set ext : ((Finset.univ.erase i) → ℝ) → Fin n → ℝ := fun z j =>
    if h : j = i then 0 else z ⟨j, Finset.mem_erase.2 ⟨h, Finset.mem_univ j⟩⟩ with hext
  have hextm : Measurable ext := by
    refine measurable_pi_lambda _ fun j => ?_
    by_cases h : j = i
    · subst h; simpa [hext] using measurable_const
    · simp only [hext, h, ↓reduceDIte]; exact measurable_pi_apply _
  have hφm : Measurable φ := continuous_abs.measurable.comp (measurable_pi_apply _)
  have hψm : Measurable (fun z => H.indicator (1 : (Fin n → ℝ) → ℝ) (ext z)) :=
    (measurable_const.indicator hH).comp hextm
  have h3 := h2.comp hφm hψm
  have h4 := h3.integral_fun_mul_eq_mul_integral
    (hφm.comp (measurable_pi_lambda _ fun j => measurable_id.comp
      (measurable_pi_apply _))).aestronglyMeasurable
    (hψm.comp (measurable_pi_lambda _ fun j => measurable_id.comp
      (measurable_pi_apply _))).aestronglyMeasurable
  have e1 : ∀ δ : Fin n → ℝ, (φ ∘ fun a (j : ({i} : Finset (Fin n))) => id (a j)) δ = |δ i| := by
    intro δ; rfl
  have e2 : ∀ δ : Fin n → ℝ, ((fun z => H.indicator (1 : (Fin n → ℝ) → ℝ) (ext z)) ∘
      fun a (j : (Finset.univ.erase i)) => id (a j)) δ = H.indicator 1 (Function.update δ i 0) := by
    intro δ
    simp only [Function.comp_apply, id]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp [hext]
    · simp [hext, h, Function.update_of_ne h]
  simp only [e1, e2] at h4
  exact h4

lemma abs_sum_mul_le' {n : ℕ} (g w : Fin n → ℝ) (G W : ℝ) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hg : ∑ i, g i ^ 2 ≤ G ^ 2) (hw : ∑ i, w i ^ 2 ≤ W ^ 2) : |∑ i, g i * w i| ≤ G * W := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g w
  have h1 : (∑ i, g i * w i) ^ 2 ≤ (G * W) ^ 2 := by
    rw [mul_pow]
    exact hcs.trans (mul_le_mul hg hw (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _))
  have h2 := Real.abs_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity)] at h2

/-- `‖δ_μ‖₂ ≤ 0.8667 ε t` for the direction of line 11 of Main. -/
lemma direction_sq_le {n : ℕ} (hn : 10 ≤ n) (x s : Fin n → ℝ) (t ε : ℝ) (ht : 0 < t)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 40000) (hap : ApproxScalar 0.1 (fun i => x i * s i) t) :
    ∑ i, direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s i ^ 2 ≤
      (0.8667 * ε * t) ^ 2 := by
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hsn : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  set α := ε / (3 * Real.sqrt n) with hα
  have hα0 : 0 < α := by positivity
  have hα1 : α ≤ 1 := by
    have : α ≤ ε := div_le_self hε.le (by nlinarith)
    linarith
  set g := potentialGrad (lam n) (fun l => x l * s l / t - 1) with hg
  set a : Fin n → ℝ := fun i => -α * (x i * s i) with ha
  set c : Fin n → ℝ := fun i => -(ε / 2 * ((1 - α) * t)) * (g i / norm2 g) with hc
  have e : ∀ i, direction (lam n) ε t ((1 - α) * t) x s i = a i + c i := by
    intro i
    simp only [direction, ha, hc, ← hg]
    field_simp
    ring
  simp only [e]
  have hA : ∑ i, a i ^ 2 ≤ (0.3667 * ε * t) ^ 2 := by
    have h1 : ∀ i, a i ^ 2 ≤ α ^ 2 * (1.1 * t) ^ 2 := by
      intro i
      have := hap i
      simp only [ha]
      rw [neg_mul, neg_sq, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by nlinarith) (by linarith) 2)
        (sq_nonneg _)
    calc ∑ i, a i ^ 2 ≤ ∑ _i : Fin n, α ^ 2 * (1.1 * t) ^ 2 := Finset.sum_le_sum fun i _ => h1 i
      _ = n * (α ^ 2 * (1.1 * t) ^ 2) := by simp
      _ = 1.21 / 9 * ε ^ 2 * t ^ 2 := by
          rw [hα]; field_simp; rw [hsn]; ring
      _ ≤ (0.3667 * ε * t) ^ 2 := by nlinarith [sq_nonneg (ε * t)]
  have hC : ∑ i, c i ^ 2 ≤ (0.5 * ε * t) ^ 2 := by
    have h2 := sum_sq_div_norm2_le' g
    have e2 : ∑ i, c i ^ 2 = (ε / 2 * ((1 - α) * t)) ^ 2 * ∑ i, (g i / norm2 g) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]; ring
    rw [e2]
    have hq0 : 0 ≤ (1 - α) * t := mul_nonneg (by linarith) ht.le
    have hq1 : (1 - α) * t ≤ t := by nlinarith
    have h3 : (ε / 2 * ((1 - α) * t)) ^ 2 ≤ (0.5 * ε * t) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by positivity) hq0)
        (by have := mul_le_mul_of_nonneg_left hq1 (show (0:ℝ) ≤ ε / 2 by positivity); linarith) 2
    calc (ε / 2 * ((1 - α) * t)) ^ 2 * ∑ i, (g i / norm2 g) ^ 2
        ≤ (0.5 * ε * t) ^ 2 * 1 := mul_le_mul h3 h2 (Finset.sum_nonneg fun i _ => sq_nonneg _)
          (sq_nonneg _)
      _ = (0.5 * ε * t) ^ 2 := mul_one _
  have hAC := abs_sum_mul_le' a c (0.3667 * ε * t) (0.5 * ε * t) (by positivity) (by positivity) hA hC
  have e3 : ∑ i, (a i + c i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * c i + ∑ i, c i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [e3]
  have := le_abs_self (∑ i, a i * c i)
  nlinarith

/-- On the success event, `|δ_i| ≤ 2 x̄_i s̄_i`: `δ̃_x/x̄ + δ̃_s/s̄ = δ̃_μ/(x̄ s̄)`. -/
lemma delta_le_on_success {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (x s v : Fin n → ℝ) (hxb : ∀ j, 0 < xbar x s v j) (hsb : ∀ j, 0 < sbar x s v j)
    (δ : Fin n → ℝ) (hδ : δ ∈ successEvent A x s v) (i : Fin n) :
    |δ i| ≤ 2 * (xbar x s v i * sbar x s v i) := by
  have hL : 1 < Real.log n := by
    have h10 : (10:ℝ) ≤ n := by exact_mod_cast hn
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log n := Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  obtain ⟨h1, h2⟩ := hδ i
  have hb : 1 / (100 * Real.log n) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hm := mul_pos (hxb i) (hsb i)
  have e : δ i = (xbar x s v i * sbar x s v i) *
      (stepS A x s v δ i / sbar x s v i + stepX A x s v δ i / xbar x s v i) := by
    have := (hxb i).ne'
    have := (hsb i).ne'
    have := (Real.sqrt_pos.2 hm).ne'
    unfold stepS stepX
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos hm]
  have h3 := abs_add_le (stepS A x s v δ i / sbar x s v i) (stepX A x s v δ i / xbar x s v i)
  have h4 : |stepS A x s v δ i / sbar x s v i + stepX A x s v δ i / xbar x s v i| ≤ 2 := by linarith
  nlinarith

lemma cont_stepX {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n) :
    Continuous (fun δ => stepX A x s v δ i) := by
  unfold stepX pMu; fun_prop

lemma cont_stepS {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (i : Fin n) :
    Continuous (fun δ => stepS A x s v δ i) := by
  unfold stepS pMu; fun_prop

lemma stepS_smul {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ) (c : ℝ)
    (j : Fin n) : stepS A x s v (c • δ) j = c * stepS A x s v δ j := by
  unfold stepS pMu
  have e : (fun l => (c • δ) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      c • (fun l => δ l / Real.sqrt (xbar x s v l * sbar x s v l)) := by
    funext l; simp [mul_div_assoc]
  rw [e, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma stepX_smul {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ) (c : ℝ)
    (j : Fin n) : stepX A x s v (c • δ) j = c * stepX A x s v δ j := by
  unfold stepX pMu
  have e : (fun l => (c • δ) l / Real.sqrt (xbar x s v l * sbar x s v l)) =
      c • (fun l => δ l / Real.sqrt (xbar x s v l * sbar x s v l)) := by
    funext l; simp [mul_div_assoc]
  rw [e, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma sampleProb_smul {n : ℕ} (k : ℝ) (δ : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) (i : Fin n) :
    sampleProb k (c • δ) i = sampleProb k δ i := by
  unfold sampleProb
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

lemma coordLaw_map (p a c : ℝ) :
    (coordLaw p a).map (fun y => c * y) = coordLaw p (c * a) := by
  unfold coordLaw
  rw [Measure.map_add _ _ (measurable_const_mul c), Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' (measurable_const_mul c), Measure.map_dirac' (measurable_const_mul c)]
  simp [mul_div_assoc]

lemma sampleLaw_smul {n : ℕ} (k : ℝ) (δ : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    sampleLaw k (c • δ) = (sampleLaw k δ).map (fun δ => c • δ) := by
  unfold sampleLaw
  have e : (fun δ : Fin n → ℝ => c • δ) = (fun x i => (fun y => c * y) (x i)) := by
    funext x i; simp
  rw [e, Measure.pi_map_pi (fun i => (measurable_const_mul c).aemeasurable)]
  congr 1; funext i
  rw [coordLaw_map, sampleProb_smul k δ c hc]
  simp

lemma integral_coord {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ δ, f (δ i) ∂(Measure.pi μs) = ∫ y, f y ∂(μs i) := by
  have := integral_map (μ := Measure.pi μs) (measurable_pi_apply i).aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [(measurePreserving_eval μs i).map_eq] at this
  exact this.symm

lemma ae_coord_le {n : ℕ} (μs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (μs j)]
    (i : Fin n) (B : ℝ) (h : μs i {y | B < |y|} = 0) :
    ∀ᵐ δ ∂(Measure.pi μs), |δ i| ≤ B := by
  rw [ae_iff]
  have hm : MeasurableSet {y : ℝ | B < |y|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have := (measurePreserving_eval μs i).measure_preimage hm.nullMeasurableSet
  simp only [not_le]
  rw [show {a : Fin n → ℝ | B < |a i|} = Function.eval i ⁻¹' {y | B < |y|} from rfl, this, h]

lemma perturb_good {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ)
    (hxb : ∀ j, 0 < xbar x s v j) (hsb : ∀ j, 0 < sbar x s v j) (c : ℝ) (hc : 0 < c)
    (hcj : ∀ j, c ≤ xbar x s v j * sbar x s v j) (u : Fin n → ℝ) (i : Fin n) (a ρ τ : ℝ)
    (ha : 2 * (|a| / c) ≤ ρ)
    (hu : ∀ j, |stepS A x s v u j / sbar x s v j| ≤ τ ∧ |stepX A x s v u j / xbar x s v j| ≤ τ) :
    ∀ j, |stepS A x s v (u + Pi.single i a) j / sbar x s v j| ≤ τ + ρ ∧
      |stepX A x s v (u + Pi.single i a) j / xbar x s v j| ≤ τ + ρ := by
  intro j
  obtain ⟨h1, h2⟩ := single_step_bound A x s v hxb hsb c hc hcj i a j
  obtain ⟨h3, h4⟩ := hu j
  rw [stepS_add, stepX_add, add_div, add_div]
  have h0 : 0 ≤ |a| / c := by positivity
  constructor
  · calc _ ≤ |stepS A x s v u j / sbar x s v j| +
          |stepS A x s v (Pi.single i a) j / sbar x s v j| := abs_add_le _ _
      _ ≤ τ + ρ := by linarith
  · calc _ ≤ |stepX A x s v u j / xbar x s v j| +
          |stepX A x s v (Pi.single i a) j / xbar x s v j| := abs_add_le _ _
      _ ≤ τ + ρ := by linarith

lemma bias_real (dm J η ηs : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ ηs) (hηs : ηs ≤ 0.002)
    (hJ : |J| ≤ |dm| * ηs) : ((1 - η)⁻¹ * (dm - J) - dm) ^ 2 ≤ (0.0041 * dm) ^ 2 := by
  have h1 : 0 < 1 - η := by linarith
  have e : (1 - η)⁻¹ * (dm - J) - dm = (η * dm - J) / (1 - η) := by field_simp; ring
  rw [e, div_pow]
  rw [div_le_iff₀ (by positivity)]
  have h2 : |η * dm - J| ≤ 2 * ηs * |dm| := by
    calc |η * dm - J| ≤ |η * dm| + |J| := abs_sub _ _
      _ = η * |dm| + |J| := by rw [abs_mul, abs_of_nonneg hη0]
      _ ≤ ηs * |dm| + |dm| * ηs := by
          have := mul_le_mul_of_nonneg_right hη (abs_nonneg dm); linarith
      _ = 2 * ηs * |dm| := by ring
  have h3 : (η * dm - J) ^ 2 ≤ (2 * ηs * |dm|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : (2 * ηs * |dm|) ^ 2 ≤ (0.004 * |dm|) ^ 2 := by
    have : 0 ≤ ηs := hη0.trans hη
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg dm]) 2
  have h5 : (0.004 * |dm|) ^ 2 ≤ (0.0041 * dm) ^ 2 * (1 - η) ^ 2 := by
    have h6 : (0.998:ℝ) ^ 2 ≤ (1 - η) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have h7 : (0.004 * |dm|) ^ 2 = 0.000016 * dm ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [h7, mul_pow]
    have : 0 ≤ dm ^ 2 := sq_nonneg _
    nlinarith
  linarith

lemma xbar_sbar {n : ℕ} (x s v δμ : Fin n → ℝ) (t k ε εmp : ℝ)
    (hAs : Assumption41 x s t v δμ k ε εmp) :
    (∀ i, 0 < xbar x s v i) ∧ (∀ i, 0 < sbar x s v i) ∧
      ∀ i, xbar x s v i * sbar x s v i = x i * s i := by
  obtain ⟨hx, hs, -, -, hεmp, -, hw, -, -, -, -, -⟩ := hAs
  have hxs : ∀ i, 0 < x i / s i := fun i => div_pos (hx i) (hs i)
  have hv : ∀ i, 0 < v i := fun i => by
    have h1 := (hw i).2
    dsimp only at h1
    by_contra hcon
    push_neg at hcon
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 1 + εmp) hcon
    linarith [hxs i]
  refine ⟨fun i => mul_pos (hx i) (Real.sqrt_pos.2 (div_pos (hv i) (hxs i))),
    fun i => mul_pos (hs i) (Real.sqrt_pos.2 (div_pos (hxs i) (hv i))), fun i => ?_⟩
  unfold xbar sbar
  have h1 := div_pos (hv i) (hxs i)
  rw [show x i * Real.sqrt (v i / (x i / s i)) * (s i * Real.sqrt (x i / s i / v i)) =
    x i * s i * (Real.sqrt (v i / (x i / s i)) * Real.sqrt (x i / s i / v i)) by ring,
    ← Real.sqrt_mul h1.le]
  have h3 : v i / (x i / s i) * (x i / s i / v i) = 1 := by
    have := (hv i).ne'; have := (hxs i).ne'; have := (hx i).ne'; have := (hs i).ne'
    field_simp
  rw [h3, Real.sqrt_one, mul_one]

set_option maxHeartbeats 1000000 in
/-- The conditioning bias: `E_P[δ̃_μ] − δ_μ` is tiny, from Claim 4.7 applied to `1.15 δ_μ`. -/
lemma bias_bound {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ) (hA : A.rank = d)
    (x s v δμ : Fin n → ℝ) (t k ε εmp : ℝ) (hAs : Assumption41 x s t v δμ k ε εmp)
    (hδ : ∑ i, δμ i ^ 2 ≤ (0.8667 * ε * t) ^ 2) :
    ∑ i, (∫ δ, δ i ∂(stepLaw A x s v k δμ) - δμ i) ^ 2 ≤ (0.01 * ε * t) ^ 2 := by
  have hL := one_lt_log hn
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  obtain ⟨hxb, hsb, hmu⟩ := xbar_sbar x s v δμ t k ε εmp hAs
  obtain ⟨hx, hs, ht, hap, hεmp, hεmp', hw, hε, hεle, hnorm, hk, hkge⟩ := hAs
  have hεL : ε * Real.log n ≤ 1 / 40000 := by
    rw [le_div_iff₀ (by positivity)] at hεle; linarith
  have hcj : ∀ j, 0.9 * t ≤ xbar x s v j * sbar x s v j := fun j => by
    rw [hmu]; have h := (hap j).1; dsimp only at h; linarith
  have hc : (0:ℝ) < 0.9 * t := by positivity
  have hpr : ∀ i, 0 < sampleProb k δμ i ∧ sampleProb k δμ i ≤ 1 := sampleProb_pos hn0 k hk δμ
  haveI hcl : ∀ i, IsProbabilityMeasure (coordLaw (sampleProb k δμ i) (δμ i)) :=
    fun i => coordLaw_isProb _ _ (hpr i).1 (hpr i).2
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = sampleLaw k δμ := ⟨_, rfl⟩
  have hQpi : Q = Measure.pi (fun i => coordLaw (sampleProb k δμ i) (δμ i)) := hQ
  haveI : IsProbabilityMeasure Q := by rw [hQpi]; infer_instance
  set L := Real.log n with hLdef
  have hL0 : 0 < L := by linarith
  have hD0 : 0 ≤ ∑ l, δμ l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hsD : Real.sqrt (∑ l, δμ l ^ 2) ≤ 0.8667 * ε * t := by
    rw [show 0.8667 * ε * t = Real.sqrt ((0.8667 * ε * t) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hδ
  have hk' : 40000000 * ε * Real.sqrt n * L ^ 2 ≤ k := by
    refine le_trans ?_ hkge
    rw [le_div_iff₀ hεmp]
    have : 0 ≤ ε * Real.sqrt n * L ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hεmp' this
    linarith
  -- size of one coordinate of the sample
  have hAi : ∀ i, |δμ i| / sampleProb k δμ i ≤ 0.0000251 * t / L := by
    intro i
    set D := ∑ l, δμ l ^ 2 with hD
    set u := Real.sqrt D with hu
    set X := k * (δμ i ^ 2 / D + 1 / (n:ℝ)) with hX
    have hX0 : 0 < X := by
      have : (0:ℝ) < 1 / n := by positivity
      have : 0 ≤ δμ i ^ 2 / D := div_nonneg (sq_nonneg _) hD0
      positivity
    have h1 : |δμ i| / sampleProb k δμ i ≤ |δμ i| + |δμ i| / X := by
      have e : sampleProb k δμ i = min 1 X := rfl
      rw [e]
      rcases min_cases (1:ℝ) X with ⟨hm, -⟩ | ⟨hm, -⟩
      · rw [hm, div_one]; have : 0 ≤ |δμ i| / X := by positivity
        linarith
      · rw [hm]; have : 0 ≤ |δμ i| := abs_nonneg _; linarith
    have hdi : |δμ i| ≤ u := Real.abs_le_sqrt (Finset.single_le_sum
      (f := fun l => δμ l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i))
    have h2 : |δμ i| / X ≤ u * Real.sqrt n / (2 * k) := by
      by_cases hD0' : D = 0
      · have h0 : δμ i ^ 2 ≤ 0 := by
          have := Finset.single_le_sum (f := fun l => δμ l ^ 2) (fun l _ => sq_nonneg _)
            (Finset.mem_univ i)
          rw [← hD, hD0'] at this; exact this
        have : δμ i = 0 := by nlinarith [sq_nonneg (δμ i)]
        rw [this, abs_zero, zero_div]; positivity
      · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hD0')
        have hu0 : 0 < u := Real.sqrt_pos.2 hDpos
        have hu2 : u ^ 2 = D := Real.sq_sqrt hD0
        have hm2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
        have ha2 : δμ i ^ 2 = |δμ i| ^ 2 := (sq_abs _).symm
        set m := Real.sqrt (n:ℝ) with hm
        have hmn : (n:ℝ) = m ^ 2 := hm2.symm
        have hm0 : 0 < m := hsq
        rw [div_le_div_iff₀ hX0 (by positivity), hX, ha2, ← hu2, hmn]
        have key : u * m * (k * (|δμ i| ^ 2 / u ^ 2 + 1 / m ^ 2)) -
            |δμ i| * (2 * k) = k * (m * |δμ i| - u) ^ 2 / (u * m) := by
          field_simp; ring
        have : 0 ≤ k * (m * |δμ i| - u) ^ 2 / (u * m) := by positivity
        linarith
    have h3 : u * Real.sqrt n / (2 * k) ≤ 0.8667 * t / (80000000 * L) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : u * Real.sqrt n * (80000000 * L) ≤
          0.8667 * ε * t * Real.sqrt n * (80000000 * L) := by
        have := mul_le_mul_of_nonneg_right hsD
          (show 0 ≤ Real.sqrt n * (80000000 * L) by positivity)
        linarith
      have hLL : L ≤ L ^ 2 := by nlinarith
      have h5 : 0.8667 * ε * t * Real.sqrt n * (80000000 * L) ≤
          0.8667 * t * (2 * (40000000 * ε * Real.sqrt n * L ^ 2)) := by
        have := mul_le_mul_of_nonneg_left hLL
          (show (0:ℝ) ≤ 0.8667 * ε * t * Real.sqrt n * 80000000 by positivity)
        linarith
      have h6 := mul_le_mul_of_nonneg_left hk' (show (0:ℝ) ≤ 0.8667 * t * 2 by positivity)
      linarith
    have h7 : u ≤ 0.8667 * t / (40000 * L) := by
      calc u ≤ 0.8667 * ε * t := hsD
        _ ≤ 0.8667 * t / (40000 * L) := by
          rw [le_div_iff₀ (by positivity)]
          have := mul_le_mul_of_nonneg_left hεL (show (0:ℝ) ≤ 0.8667 * t by positivity)
          linarith
    have h8 : 0.8667 * t / (40000 * L) + 0.8667 * t / (80000000 * L) ≤ 0.0000251 * t / L := by
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 < t * L ^ 2 := by positivity
      nlinarith
    linarith
  -- the good sets
  set τ0 := 1 / (100 * L) with hτ0
  set ρ := 0.0001 / L with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  obtain ⟨Gd, hGd⟩ : ∃ Gd : ℝ → Set (Fin n → ℝ), Gd = fun τ => {δ | ∀ j,
      |stepS A x s v δ j / sbar x s v j| ≤ τ ∧ |stepX A x s v δ j / xbar x s v j| ≤ τ} :=
    ⟨_, rfl⟩
  have hGdm : ∀ τ, MeasurableSet (Gd τ) := by
    intro τ
    have e : Gd τ = ⋂ j, ({δ | |stepS A x s v δ j / sbar x s v j| ≤ τ} ∩
        {δ | |stepX A x s v δ j / xbar x s v j| ≤ τ}) := by
      rw [hGd]; ext δ; simp
    rw [e]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le ((cont_stepS A x s v j).div_const _).abs.measurable measurable_const).inter
      (measurableSet_le ((cont_stepX A x s v j).div_const _).abs.measurable measurable_const)
  have hS : successEvent A x s v = Gd τ0 := by rw [hGd]; rfl
  have hSm : MeasurableSet (successEvent A x s v) := by rw [hS]; exact hGdm _
  have hρA : ∀ i (a : ℝ), |a| ≤ |δμ i| / sampleProb k δμ i → 2 * (|a| / (0.9 * t)) ≤ ρ := by
    intro i a ha
    have h0 := ha.trans (hAi i)
    have h1 : |a| / (0.9 * t) ≤ (0.0000251 * t / L) / (0.9 * t) :=
      div_le_div_of_nonneg_right h0 hc.le
    have h2 : (0.0000251 * t / L) / (0.9 * t) = 0.0000251 / 0.9 / L := by
      field_simp
    have h3 : 2 * (0.0000251 / 0.9 / L) ≤ 0.0001 / L := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by norm_num) hL0.le
    rw [hρ]; linarith
  have hsplit : ∀ (δ : Fin n → ℝ) i, δ = Function.update δ i 0 + Pi.single i (δ i) := by
    intro δ i; funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h, Function.update_of_ne h]
  have hsplit' : ∀ (δ : Fin n → ℝ) i, Function.update δ i 0 = δ + Pi.single i (-δ i) := by
    intro δ i; funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h, Function.update_of_ne h]
  have P1 : ∀ (δ : Fin n → ℝ) i τ, |δ i| ≤ |δμ i| / sampleProb k δμ i →
      Function.update δ i 0 ∈ Gd τ → δ ∈ Gd (τ + ρ) := by
    intro δ i τ hδ hu
    simp only [hGd, Set.mem_setOf_eq] at hu ⊢
    have := perturb_good A x s v hxb hsb (0.9 * t) hc hcj (Function.update δ i 0) i (δ i) ρ τ
      (hρA i _ hδ) hu
    rwa [← hsplit δ i] at this
  have P2 : ∀ (δ : Fin n → ℝ) i τ, |δ i| ≤ |δμ i| / sampleProb k δμ i →
      δ ∈ Gd τ → Function.update δ i 0 ∈ Gd (τ + ρ) := by
    intro δ i τ hδ hu
    simp only [hGd, Set.mem_setOf_eq] at hu ⊢
    have := perturb_good A x s v hxb hsb (0.9 * t) hc hcj δ i (-δ i) ρ τ
      (by rw [abs_neg]; exact hρA i _ hδ) hu
    rwa [← hsplit' δ i] at this
  have hsupp : ∀ i, ∀ᵐ δ ∂Q, |δ i| ≤ |δμ i| / sampleProb k δμ i := by
    intro i; rw [hQpi]
    exact ae_coord_le _ i _ (coordLaw_bad _ _ (hpr i).1)
  -- Claim 4.7 at `1.15 δ_μ`
  have hnorm' : norm2 ((1.15:ℝ) • δμ) ≤ ε * t := by
    unfold norm2
    have e : ∑ i, ((1.15:ℝ) • δμ) i ^ 2 = 1.3225 * ∑ i, δμ i ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    calc Real.sqrt (1.3225 * ∑ i, δμ i ^ 2) ≤ Real.sqrt ((ε * t) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [hδ, sq_nonneg (ε * t)])
      _ = ε * t := Real.sqrt_sq (by positivity)
  have hAs2 : Assumption41 x s t v ((1.15:ℝ) • δμ) k ε εmp :=
    ⟨hx, hs, ht, hap, hεmp, hεmp', hw, hε, hεle, hnorm', hk, hkge⟩
  obtain ⟨-, h47⟩ := success_probability hn A hA x s v ((1.15:ℝ) • δμ) t k ε εmp hAs2
  rw [sampleLaw_smul k δμ 1.15 (by norm_num), ← hQ] at h47
  set ηs := 2 * n * Real.exp (-(0.003 * k / (ε * Real.sqrt n * Real.log n))) with hηs
  have hηs0 : 0 ≤ ηs := by positivity
  have hηs2 : ηs ≤ 0.002 := by
    have hy : 4 * L ≤ 0.003 * k / (ε * Real.sqrt n * L) := by
      rw [le_div_iff₀ (by positivity)]
      have : 0 ≤ ε * Real.sqrt n * L ^ 2 := by positivity
      nlinarith
    have h1 : Real.exp (-(0.003 * k / (ε * Real.sqrt n * L))) ≤ Real.exp (-(4 * L)) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-(4 * L)) = ((n:ℝ) ^ 4)⁻¹ := by
      rw [Real.exp_neg, show 4 * L = ((4:ℕ):ℝ) * L by norm_num, Real.exp_nat_mul, hLdef,
        Real.exp_log (by linarith)]
    have h3 : 2 * (n:ℝ) * ((n:ℝ) ^ 4)⁻¹ ≤ 0.002 := by
      rw [show 2 * (n:ℝ) * ((n:ℝ) ^ 4)⁻¹ = 2 / (n:ℝ) ^ 3 by field_simp]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10) hn' 3]
    calc ηs = 2 * n * Real.exp (-(0.003 * k / (ε * Real.sqrt n * L))) := rfl
      _ ≤ 2 * n * ((n:ℝ) ^ 4)⁻¹ := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 0.002 := h3
  have hgood : ENNReal.ofReal (1 - ηs) ≤ Q (Gd (τ0 - ρ - ρ)) := by
    have hsub : ∀ δ : Fin n → ℝ, (∀ i, |stepS A x s v δ i / sbar x s v i| ≤ 0.01 / Real.log n ∧
        |stepS A x s v δ i / s i| ≤ 0.02 / Real.log n ∧
        |stepX A x s v δ i / xbar x s v i| ≤ 0.01 / Real.log n ∧
        |stepX A x s v δ i / x i| ≤ 0.02 / Real.log n ∧
        |δ i / (x i * s i)| ≤ 0.02 / Real.log n) → δ ∈ Gd (0.01 / L) := by
      intro δ hδ
      simp only [hGd, Set.mem_setOf_eq]
      exact fun j => ⟨(hδ j).1, (hδ j).2.2.1⟩
    refine h47.trans ((measure_mono hsub).trans ?_)
    rw [Measure.map_apply (measurable_const_smul _) (hGdm _)]
    apply measure_mono
    intro δ hδ
    simp only [Set.mem_preimage, hGd, Set.mem_setOf_eq] at hδ ⊢
    have hb : 0.01 / L / 1.15 ≤ τ0 - ρ - ρ := by
      rw [hτ0, hρ]
      have e1 : 0.01 / L / 1.15 = (0.01 / 1.15) / L := by ring
      have e2 : 1 / (100 * L) - 0.0001 / L - 0.0001 / L = 0.0098 / L := by
        field_simp; ring
      rw [e1, e2]; exact div_le_div_of_nonneg_right (by norm_num) hL0.le
    intro j
    obtain ⟨h1, h2⟩ := hδ j
    rw [stepS_smul, mul_div_assoc, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.15)] at h1
    rw [stepX_smul, mul_div_assoc, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.15)] at h2
    constructor
    · have : |stepS A x s v δ j / sbar x s v j| ≤ 0.01 / L / 1.15 := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
    · have : |stepX A x s v δ j / xbar x s v j| ≤ 0.01 / L / 1.15 := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
  have hQG : Q.real (Gd (τ0 - ρ - ρ))ᶜ ≤ ηs := by
    rw [probReal_compl_eq_one_sub (hGdm _)]
    have := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hgood
    simp only [Measure.real]; linarith
  -- moments of one coordinate
  have hint : ∀ i, Integrable (fun δ : Fin n → ℝ => δ i) Q := fun i =>
    Integrable.of_bound (continuous_apply i).aestronglyMeasurable _
      (by filter_upwards [hsupp i] with δ hδ; rw [Real.norm_eq_abs]; exact hδ)
  have hEi : ∀ i, ∫ δ, δ i ∂Q = δμ i := by
    intro i
    have h1 := integral_coord (fun j => coordLaw (sampleProb k δμ j) (δμ j)) i (fun y => y)
      measurable_id
    rw [hQpi, h1, integral_coordLaw _ _ (hpr i).1 (hpr i).2]
    have := (hpr i).1.ne'
    field_simp; ring
  have hEabs : ∀ i, ∫ δ, |δ i| ∂Q = |δμ i| := by
    intro i
    have h1 := integral_coord (fun j => coordLaw (sampleProb k δμ j) (δμ j)) i (fun y => |y|)
      continuous_abs.measurable
    rw [hQpi, h1, integral_coordLaw _ _ (hpr i).1 (hpr i).2, abs_div, abs_of_pos (hpr i).1,
      abs_zero]
    have := (hpr i).1.ne'
    field_simp; ring
  have hJ : ∀ i, |∫ δ in (successEvent A x s v)ᶜ, δ i ∂Q| ≤ |δμ i| * ηs := by
    intro i
    have hupd : Measurable (fun δ : Fin n → ℝ => Function.update δ i 0) := by
      refine measurable_pi_lambda _ fun j => ?_
      by_cases h : j = i
      · subst h; simpa using measurable_const
      · simp only [Function.update_of_ne h]; exact measurable_pi_apply j
    have hH : MeasurableSet (Gd (τ0 - ρ))ᶜ := (hGdm _).compl
    have hpt : ∀ᵐ δ ∂Q, (successEvent A x s v)ᶜ.indicator (fun δ => |δ i|) δ ≤
        |δ i| * (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0) := by
      filter_upwards [hsupp i] with δ hδ
      by_cases hmem : δ ∈ (successEvent A x s v)ᶜ
      · rw [Set.indicator_of_mem hmem]
        have : Function.update δ i 0 ∈ (Gd (τ0 - ρ))ᶜ := by
          intro hu
          apply hmem
          have := P1 δ i (τ0 - ρ) hδ hu
          rw [hS]; simpa using this
        rw [Set.indicator_of_mem this]; simp
      · rw [Set.indicator_of_notMem hmem]
        exact mul_nonneg (abs_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hI1 : Integrable (fun δ : Fin n → ℝ =>
        |δ i| * (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0)) Q := by
      refine Integrable.of_bound ?_ (|δμ i| / sampleProb k δμ i) ?_
      · exact ((continuous_apply i).abs.measurable.mul
          ((measurable_const.indicator hH).comp hupd)).aestronglyMeasurable
      · filter_upwards [hsupp i] with δ hδ
        rw [Real.norm_eq_abs, abs_mul, abs_abs]
        have h0 : 0 ≤ (Gd (τ0 - ρ))ᶜ.indicator (1 : (Fin n → ℝ) → ℝ) (Function.update δ i 0) :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) _
        have h1 : (Gd (τ0 - ρ))ᶜ.indicator (1 : (Fin n → ℝ) → ℝ) (Function.update δ i 0) ≤ 1 :=
          Set.indicator_le_self' (fun _ _ => zero_le_one) _
        rw [abs_of_nonneg h0]
        calc |δ i| * (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0) ≤ |δ i| * 1 :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact hδ
    have hind := indep_update (fun j => coordLaw (sampleProb k δμ j) (δμ j)) i _ hH
    rw [← hQpi] at hind
    calc |∫ δ in (successEvent A x s v)ᶜ, δ i ∂Q|
        ≤ ∫ δ in (successEvent A x s v)ᶜ, |δ i| ∂Q := abs_integral_le_integral_abs
      _ = ∫ δ, (successEvent A x s v)ᶜ.indicator (fun δ => |δ i|) δ ∂Q :=
          (integral_indicator hSm.compl).symm
      _ ≤ ∫ δ, |δ i| * (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0) ∂Q :=
          integral_mono_ae ((hint i).abs.indicator hSm.compl) hI1 hpt
      _ = (∫ δ, |δ i| ∂Q) * ∫ δ, (Gd (τ0 - ρ))ᶜ.indicator 1 (Function.update δ i 0) ∂Q := hind
      _ ≤ |δμ i| * ηs := by
          rw [hEabs i]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have e : (fun δ : Fin n → ℝ =>
              (Gd (τ0 - ρ))ᶜ.indicator (1 : (Fin n → ℝ) → ℝ) (Function.update δ i 0)) =
              ((fun δ => Function.update δ i 0) ⁻¹' (Gd (τ0 - ρ))ᶜ).indicator 1 := by
            funext δ; rfl
          rw [e, integral_indicator_one (hupd hH)]
          refine le_trans ?_ hQG
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          apply measure_mono_ae
          filter_upwards [hsupp i] with δ hδ
          intro hmem hg
          apply hmem
          have := P2 δ i (τ0 - ρ - ρ) hδ hg
          simpa using this
  -- assembly
  have hcond : ∀ i, ∫ δ, δ i ∂(stepLaw A x s v k δμ) =
      (Q.real (successEvent A x s v))⁻¹ * (δμ i - ∫ δ in (successEvent A x s v)ᶜ, δ i ∂Q) := by
    intro i
    have h1 := integral_add_compl hSm (hint i)
    rw [hEi i] at h1
    unfold stepLaw
    rw [← hQ, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
    simp only [Measure.real]
    congr 1
    linarith
  have hη : Q.real (successEvent A x s v)ᶜ ≤ ηs := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hQG
    rw [hS]
    exact Set.compl_subset_compl.2 (fun δ hδ => by
      simp only [hGd, Set.mem_setOf_eq] at hδ ⊢
      exact fun j => ⟨(hδ j).1.trans (by linarith), (hδ j).2.trans (by linarith)⟩)
  have hQS : Q.real (successEvent A x s v) = 1 - Q.real (successEvent A x s v)ᶜ := by
    rw [probReal_compl_eq_one_sub hSm]; ring
  have hterm : ∀ i, (∫ δ, δ i ∂(stepLaw A x s v k δμ) - δμ i) ^ 2 ≤ (0.0041 * δμ i) ^ 2 := by
    intro i
    rw [hcond i, hQS]
    exact bias_real (δμ i) _ _ ηs measureReal_nonneg hη hηs2 (hJ i)
  calc ∑ i, (∫ δ, δ i ∂(stepLaw A x s v k δμ) - δμ i) ^ 2
      ≤ ∑ i, (0.0041 * δμ i) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = 0.0041 ^ 2 * ∑ i, δμ i ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (0.01 * ε * t) ^ 2 := by nlinarith [hδ, sq_nonneg (ε * t)]

end CohenLeeSongLP.StochCentralPath.L413

open CohenLeeSongLP.StochCentralPath in
theorem solution {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : A.rank = d) (x s v : Fin n → ℝ) (t kSamp ε εmp : ℝ)
    (hAs : Assumption41 x s t v
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s) kSamp ε εmp) :
    IsProbabilityMeasure (stepLaw A x s v kSamp
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s)) ∧
    ∫ δ, potential (lam n)
        (fun i => muNew A x s v δ i / ((1 - ε / (3 * Real.sqrt n)) * t) - 1)
        ∂(stepLaw A x s v kSamp (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s))
      ≤ potential (lam n) (fun i => x i * s i / t - 1) -
        lam n * ε / (15 * Real.sqrt n) *
          (potential (lam n) (fun i => x i * s i / t - 1) - 10 * n) := by
  obtain ⟨hP, he, -, hvar, hsup⟩ := mu_new_bounds hn A hA x s v _ t kSamp ε εmp hAs
  refine ⟨hP, ?_⟩
  obtain ⟨hxb, hsb, hmu⟩ := L413.xbar_sbar x s v _ t kSamp ε εmp hAs
  have hAs' := hAs
  obtain ⟨hx, hs, ht, hap, hεmp, hεmp', hw, hε, hεle, hnorm, hk, hkge⟩ := hAs'
  have hL := L413.one_lt_log hn
  have hε1 : ε ≤ 1 / 40000 := by
    have hεL : ε * Real.log n ≤ 1 / 40000 := by
      rw [le_div_iff₀ (by positivity)] at hεle; linarith
    nlinarith
  have hδsq := L413.direction_sq_le hn x s t ε ht hε hε1 hap
  have hb := L413.bias_bound hn A hA x s v _ t kSamp ε εmp hAs hδsq
  have hSm : MeasurableSet (successEvent A x s v) := by
    have e : successEvent A x s v = ⋂ j, ({δ | |stepS A x s v δ j / sbar x s v j| ≤
        1 / (100 * Real.log n)} ∩ {δ | |stepX A x s v δ j / xbar x s v j| ≤
        1 / (100 * Real.log n)}) := by
      ext δ; simp [successEvent]
    rw [e]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le ((L413.cont_stepS A x s v j).div_const _).abs.measurable
        measurable_const).inter
      (measurableSet_le ((L413.cont_stepX A x s v j).div_const _).abs.measurable
        measurable_const)
  have hδbd : ∀ᵐ δ ∂(stepLaw A x s v kSamp
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s)),
      ∀ i, |δ i| ≤ ∑ j, 2 * (xbar x s v j * sbar x s v j) := by
    filter_upwards [ae_cond_mem hSm] with δ hδ i
    exact (L413.delta_le_on_success hn A x s v hxb hsb δ hδ i).trans
      (Finset.single_le_sum (f := fun j => 2 * (xbar x s v j * sbar x s v j))
        (fun j _ => by have := mul_pos (hxb j) (hsb j); positivity) (Finset.mem_univ i))
  have hsup' : ∀ᵐ δ ∂(stepLaw A x s v kSamp
      (direction (lam n) ε t ((1 - ε / (3 * Real.sqrt n)) * t) x s)),
      ∀ i, |(muNew A x s v δ i - x i * s i) / (x i * s i)| ≤ 0.021 / Real.log n := by
    filter_upwards [ae_cond_mem hSm] with δ hδ
    exact hsup δ hδ
  have hMn : ∀ i, Continuous fun δ => muNew A x s v δ i := fun i => by
    unfold muNew stepX stepS pMu; fun_prop
  have hμ : ∀ i, 0.9 * t ≤ (fun i => x i * s i) i ∧ (fun i => x i * s i) i ≤ 1.1 * t := by
    intro i
    have h := hap i
    dsimp only at h ⊢
    constructor <;> linarith [h.1, h.2]
  exact L413.core hn _ (muNew A x s v) hMn (fun i => x i * s i) _ t ε εmp kSamp ht hε hεle
    hεmp hεmp' hkge hμ (fun i => rfl) hsup' _ hδbd he hvar hb
