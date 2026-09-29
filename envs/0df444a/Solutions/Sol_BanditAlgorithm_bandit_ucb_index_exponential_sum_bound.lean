-- Prove2me | solution 1 for BanditAlgorithm.bandit_ucb_index_exponential_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-07-20T17:58:55.287802+00:00
-- url     : https://prove2.me/submissions/ed45a4de-dd80-424c-86a1-10c22d57d307

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
Analytic scratch work for Bandit Algorithms, printed pp. 118--119 (PDF pp. 127--128),
Lemma 8.2. The source splits at `u = 2 a ε⁻²`, compares the decreasing exponential
tail with an integral, and then substitutes `s = ε √t - √(2a)`.
-/

open Filter MeasureTheory Real Set

namespace Lemma82Proof

lemma sqrt_threshold_lt {t ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (ht : 2 * a / ε ^ 2 < t) : Real.sqrt (2 * a / t) < ε := by
  rw [Real.sqrt_lt' hε]
  have ht0 : 0 < t := by
    have hcut : 0 < 2 * a / ε ^ 2 := by positivity
    linarith
  rw [div_lt_iff₀ ht0]
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  rw [div_lt_iff₀ hε2] at ht
  nlinarith

lemma exponent_eq_shifted {t ε a : ℝ} (ht : 0 < t) (ha : 0 ≤ a) :
    -((t * (ε - Real.sqrt (2 * a / t))) ^ 2) / ((2 : ℝ) * t * 1) =
      -((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2 := by
  rw [Real.sqrt_div (by positivity : 0 ≤ 2 * a) t]
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  field_simp
  nlinarith

lemma shifted_sqrt_nonneg {t ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (ht : 2 * a / ε ^ 2 ≤ t) : 0 ≤ ε * Real.sqrt t - Real.sqrt (2 * a) := by
  have hε0 : 0 ≤ ε := hε.le
  have ht0 : 0 ≤ t := by
    have hcut : 0 < 2 * a / ε ^ 2 := by positivity
    linarith
  have hsq : Real.sqrt (2 * a) ≤ Real.sqrt (ε ^ 2 * t) := by
    apply Real.sqrt_le_sqrt
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    rw [div_le_iff₀ hε2] at ht
    nlinarith
  rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε0] at hsq
  exact sub_nonneg.mpr hsq

lemma shifted_gaussian_antitone {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    AntitoneOn (fun t : ℝ ↦
      Real.exp (-((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2))
      (Set.Ici (2 * a / ε ^ 2)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := by
    have hcut : 0 < 2 * a / ε ^ 2 := by positivity
    exact hcut.le.trans hx
  have hsqrt : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hu : 0 ≤ ε * Real.sqrt x - Real.sqrt (2 * a) :=
    shifted_sqrt_nonneg hε ha hx
  have huv : ε * Real.sqrt x - Real.sqrt (2 * a) ≤
      ε * Real.sqrt y - Real.sqrt (2 * a) := by
    nlinarith
  have hsq : (ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2 ≤
      (ε * Real.sqrt y - Real.sqrt (2 * a)) ^ 2 := by
    nlinarith
  apply Real.exp_le_exp.mpr
  nlinarith

lemma finite_tail_sum_le_integral {m n : ℕ} {ε a : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (hmn : m ≤ n)
    (hm : 2 * a / ε ^ 2 ≤ (m : ℝ)) :
    (∑ i ∈ Finset.Ico m n,
      Real.exp (-((ε * Real.sqrt (i + 1 : ℕ) - Real.sqrt (2 * a)) ^ 2) / 2)) ≤
      ∫ x in (m : ℝ)..n,
        Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2) := by
  have hanti : AntitoneOn (fun x : ℝ ↦
      Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2))
      (Set.Icc (m : ℝ) n) :=
    (shifted_gaussian_antitone hε ha).mono fun x hx ↦ hm.trans hx.1
  simpa only [Nat.cast_add, Nat.cast_one] using
    AntitoneOn.sum_le_integral_Ico hmn hanti

lemma integral_x_mul_exp_neg_half_sq :
    ∫ x : ℝ in Set.Ioi 0, x * Real.exp (-(1 / 2 : ℝ) * x ^ 2) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (1 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_one] at h ⊢
  simpa only [Real.rpow_one] using h

lemma integral_exp_neg_half_sq :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
      Real.sqrt (Real.pi / (1 / 2 : ℝ)) / 2 := by
  simpa using integral_gaussian_Ioi (1 / 2 : ℝ)

lemma integral_shifted_gaussian_closed {a : ℝ} :
    ∫ x : ℝ in Set.Ioi 0,
        (x + Real.sqrt (2 * a)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
      1 + Real.sqrt (Real.pi * a) := by
  calc
    _ = (∫ x : ℝ in Set.Ioi 0, x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) +
        ∫ x : ℝ in Set.Ioi 0,
          Real.sqrt (2 * a) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
      rw [← integral_add]
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        ring
      · exact (integrable_mul_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
      · exact ((integrable_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _).integrableOn
    _ = 1 + Real.sqrt (2 * a) * (Real.sqrt (Real.pi / (1 / 2 : ℝ)) / 2) := by
      rw [integral_x_mul_exp_neg_half_sq, integral_const_mul,
        integral_exp_neg_half_sq]
    _ = 1 + Real.sqrt (Real.pi * a) := by
      congr 1
      rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) a]
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) Real.pi]
      rw [Real.sqrt_mul Real.pi_pos.le a]
      have hsqrt2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc
        Real.sqrt 2 * Real.sqrt a * (Real.sqrt 2 * Real.sqrt Real.pi / 2) =
            (Real.sqrt 2 ^ 2 / 2) * (Real.sqrt Real.pi * Real.sqrt a) := by ring
        _ = Real.sqrt Real.pi * Real.sqrt a := by rw [hsqrt2]; ring

lemma integrableOn_shifted_gaussian (a : ℝ) :
    IntegrableOn (fun x : ℝ ↦
      (x + Real.sqrt (2 * a)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) (Set.Ioi 0) := by
  have h1 : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
      (Set.Ioi 0) := (integrable_mul_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
  have h2 : IntegrableOn (fun x : ℝ ↦
      Real.sqrt (2 * a) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) (Set.Ioi 0) :=
    ((integrable_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (Real.sqrt (2 * a))).integrableOn
  refine (h1.add h2).congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

lemma gaussian_substitution_zero {ε a : ℝ} (ha : 0 ≤ a) :
    ((Real.sqrt (2 * a)) / ε) ^ 2 = 2 * a / ε ^ 2 := by
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * a)]

lemma gaussian_substitution_hasDerivAt {ε a s : ℝ} (hε : 0 < ε) :
    HasDerivAt (fun x : ℝ ↦ ((x + Real.sqrt (2 * a)) / ε) ^ 2)
      (2 * (s + Real.sqrt (2 * a)) / ε ^ 2) s := by
  refine ((((hasDerivAt_id' s).add_const (Real.sqrt (2 * a))).div_const ε).pow 2).congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp

lemma gaussian_substitution_tendsto {ε a : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ ↦ ((x + Real.sqrt (2 * a)) / ε) ^ 2) atTop atTop := by
  apply (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
  exact Tendsto.atTop_div_const hε
    (tendsto_atTop_add_const_right atTop (Real.sqrt (2 * a)) tendsto_id)

lemma gaussian_substitution_continuous {ε a : ℝ} :
    Continuous (fun x : ℝ ↦ ((x + Real.sqrt (2 * a)) / ε) ^ 2) := by
  fun_prop

lemma gaussian_substitution_strictMonoOn {ε a : ℝ} (hε : 0 < ε) :
    StrictMonoOn (fun x : ℝ ↦ ((x + Real.sqrt (2 * a)) / ε) ^ 2) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hxq : 0 ≤ (x + Real.sqrt (2 * a)) / ε :=
    (div_pos (add_pos_of_pos_of_nonneg hx (Real.sqrt_nonneg _)) hε).le
  have hyq : 0 ≤ (y + Real.sqrt (2 * a)) / ε :=
    (div_pos (add_pos_of_pos_of_nonneg hy (Real.sqrt_nonneg _)) hε).le
  rw [sq_lt_sq₀ hxq hyq]
  exact (div_lt_div_iff_of_pos_right hε).2 (by linarith)

lemma gaussian_substitution_image {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    (fun x : ℝ ↦ ((x + Real.sqrt (2 * a)) / ε) ^ 2) '' Set.Ioi 0 =
      Set.Ioi (2 * a / ε ^ 2) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : 0 < s := Set.mem_Ioi.mp hs
    rw [Set.mem_Ioi]
    rw [← gaussian_substitution_zero (ε := ε) ha.le]
    have hq0 : 0 ≤ Real.sqrt (2 * a) / ε :=
      div_nonneg (Real.sqrt_nonneg _) hε.le
    have hqs : 0 ≤ (s + Real.sqrt (2 * a)) / ε :=
      (div_pos (add_pos_of_pos_of_nonneg hs' (Real.sqrt_nonneg _)) hε).le
    rw [sq_lt_sq₀ hq0 hqs]
    exact (div_lt_div_iff_of_pos_right hε).2 (by linarith [hs'])
  · intro ht
    have ht' : 2 * a / ε ^ 2 < t := Set.mem_Ioi.mp ht
    have ht0 : 0 < t := by
      have hcut : 0 < 2 * a / ε ^ 2 := by positivity
      linarith [ht']
    let s := ε * Real.sqrt t - Real.sqrt (2 * a)
    have hs : 0 < s := by
      have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
      rw [div_lt_iff₀ hε2] at ht'
      have hc_sq : Real.sqrt (2 * a) ^ 2 = 2 * a :=
        Real.sq_sqrt (by positivity)
      have hr_sq : (ε * Real.sqrt t) ^ 2 = ε ^ 2 * t := by
        rw [mul_pow, Real.sq_sqrt ht0.le]
      have hc0 : 0 ≤ Real.sqrt (2 * a) := Real.sqrt_nonneg _
      have hr0 : 0 ≤ ε * Real.sqrt t := mul_nonneg hε.le (Real.sqrt_nonneg _)
      have hroot : Real.sqrt (2 * a) < ε * Real.sqrt t := by
        rw [← sq_lt_sq₀ hc0 hr0, hc_sq, hr_sq]
        nlinarith [ht']
      dsimp [s]
      exact sub_pos.mpr hroot
    refine ⟨s, hs, ?_⟩
    have hquot : (s + Real.sqrt (2 * a)) / ε = Real.sqrt t := by
      dsimp [s]
      field_simp [ne_of_gt hε]
      ring
    change ((s + Real.sqrt (2 * a)) / ε) ^ 2 = t
    rw [hquot, Real.sq_sqrt ht0.le]

lemma gaussian_integrand_comp {ε a s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    Real.exp (-((ε * Real.sqrt (((s + Real.sqrt (2 * a)) / ε) ^ 2) -
        Real.sqrt (2 * a)) ^ 2) / 2) =
      Real.exp (-(1 / 2 : ℝ) * s ^ 2) := by
  have hq : 0 < (s + Real.sqrt (2 * a)) / ε := by positivity
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
  have heq : ε * ((s + Real.sqrt (2 * a)) / ε) - Real.sqrt (2 * a) = s := by
    field_simp [ne_of_gt hε]
    ring
  rw [heq]
  congr 1
  ring

lemma integral_shifted_tail_closed {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∫ t : ℝ in Set.Ioi (2 * a / ε ^ 2),
        Real.exp (-((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2) =
      2 / ε ^ 2 * (1 + Real.sqrt (Real.pi * a)) := by
  let f : ℝ → ℝ := fun x ↦ ((x + Real.sqrt (2 * a)) / ε) ^ 2
  let f' : ℝ → ℝ := fun x ↦ 2 * (x + Real.sqrt (2 * a)) / ε ^ 2
  let g : ℝ → ℝ := fun t ↦
    Real.exp (-((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2)
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (f := f) (f' := f') (g := g) measurableSet_Ioi
    (fun x hx ↦ (gaussian_substitution_hasDerivAt (ε := ε) (a := a) (s := x) hε).hasDerivWithinAt)
    (gaussian_substitution_strictMonoOn (ε := ε) (a := a) hε).injOn
  rw [gaussian_substitution_image hε ha] at hchange
  calc
    ∫ t : ℝ in Set.Ioi (2 * a / ε ^ 2), g t =
        ∫ s : ℝ in Set.Ioi 0, |f' s| • g (f s) := hchange
    _ = ∫ s : ℝ in Set.Ioi 0,
        (2 / ε ^ 2) * ((s + Real.sqrt (2 * a)) *
          Real.exp (-(1 / 2 : ℝ) * s ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hs0 : 0 < s := hs
      have hfp : 0 < f' s := by
        dsimp [f']
        positivity
      change |f' s| * g (f s) = _
      rw [abs_of_pos hfp]
      dsimp [f, f', g]
      rw [gaussian_integrand_comp hε hs0]
      ring
    _ = (2 / ε ^ 2) *
        ∫ s : ℝ in Set.Ioi 0,
          (s + Real.sqrt (2 * a)) * Real.exp (-(1 / 2 : ℝ) * s ^ 2) := by
      rw [integral_const_mul]
    _ = 2 / ε ^ 2 * (1 + Real.sqrt (Real.pi * a)) := by
      rw [integral_shifted_gaussian_closed]

lemma integrableOn_shifted_tail {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦
      Real.exp (-((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2))
      (Set.Ioi (2 * a / ε ^ 2)) := by
  let f : ℝ → ℝ := fun x ↦ ((x + Real.sqrt (2 * a)) / ε) ^ 2
  let f' : ℝ → ℝ := fun x ↦ 2 * (x + Real.sqrt (2 * a)) / ε ^ 2
  let g : ℝ → ℝ := fun t ↦
    Real.exp (-((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2)
  have himage := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := f) (f' := f') measurableSet_Ioi
    (fun x hx ↦ (gaussian_substitution_hasDerivAt (ε := ε) (a := a) (s := x) hε).hasDerivWithinAt)
    (gaussian_substitution_strictMonoOn (ε := ε) (a := a) hε).injOn g
  rw [gaussian_substitution_image hε ha] at himage
  apply himage.mpr
  have hbase := (integrableOn_shifted_gaussian a).const_mul (2 / ε ^ 2)
  apply IntegrableOn.congr_fun hbase
  · intro s hs
    have hs0 : 0 < s := Set.mem_Ioi.mp hs
    have hfp : 0 < f' s := by
      dsimp [f']
      positivity
    change (2 / ε ^ 2) * ((s + Real.sqrt (2 * a)) *
      Real.exp (-(1 / 2 : ℝ) * s ^ 2)) = |f' s| * g (f s)
    symm
    rw [abs_of_pos hfp]
    dsimp [f, f', g]
    rw [gaussian_integrand_comp hε hs0]
    ring
  · exact measurableSet_Ioi

lemma sum_Icc_eq_first_add_shift {f : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n) :
    (∑ t ∈ Finset.Icc m n, f t) =
      f m + ∑ i ∈ Finset.Ico m n, f (i + 1) := by
  have hins : m ∉ Finset.Icc (m + 1) n := by simp
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hmn, Finset.sum_insert hins]
  congr 1
  have himage : (Finset.Ico m n).image (fun i ↦ i + 1) = Finset.Icc (m + 1) n := by
    ext t
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_Icc]
    constructor
    · rintro ⟨i, ⟨hmi, hin⟩, rfl⟩
      omega
    · intro ht
      refine ⟨t - 1, ?_, by omega⟩
      omega
  rw [← himage, Finset.sum_image]
  intro x hx y hy hxy
  exact Nat.add_right_cancel hxy

end Lemma82Proof

open Lemma82Proof
theorem solution
    {n : ℕ} {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    (∑ t ∈ Finset.Icc 1 n,
      if 2 * a / ε ^ 2 < (t : ℝ) then
        Real.exp (-((t : ℝ) * (ε - Real.sqrt (2 * a / t))) ^ 2 /
          ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
      else 1) ≤
      1 + 2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) := by
  let u : ℝ := 2 * a / ε ^ 2
  let q : ℕ := ⌊u⌋₊
  let m : ℕ := q + 1
  let F : ℕ → ℝ := fun t ↦
    Real.exp (-((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2)
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hq : (q : ℝ) ≤ u := by
    dsimp [q]
    exact Nat.floor_le hu
  have hum : u < (m : ℝ) := by
    dsimp [m, q]
    exact_mod_cast Nat.lt_floor_add_one u
  have hm1 : 1 ≤ m := by simp [m]
  have hcond (t : ℕ) : u < (t : ℝ) ↔ m ≤ t := by
    dsimp [m, q]
    rw [Nat.add_one_le_iff, Nat.floor_lt hu]
  have hsummand (t : ℕ) (ht : t ∈ Finset.Icc 1 n) :
      (if 2 * a / ε ^ 2 < (t : ℝ) then
          Real.exp (-((t : ℝ) * (ε - Real.sqrt (2 * a / t))) ^ 2 /
            ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
        else 1) = if m ≤ t then F t else 1 := by
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t from ht1)
    by_cases hcut : u < (t : ℝ)
    · have hmt : m ≤ t := (hcond t).mp hcut
      simp only [u] at hcut
      simp only [hcut, hmt, ↓reduceIte, F]
      rw [exponent_eq_shifted ht0 ha.le]
    · have hmt : ¬ m ≤ t := fun h ↦ hcut ((hcond t).mpr h)
      simp only [u] at hcut
      simp [hcut, hmt]
  have hrepl :
      (∑ t ∈ Finset.Icc 1 n,
        if 2 * a / ε ^ 2 < (t : ℝ) then
          Real.exp (-((t : ℝ) * (ε - Real.sqrt (2 * a / t))) ^ 2 /
            ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
        else 1) =
      ∑ t ∈ Finset.Icc 1 n, if m ≤ t then F t else 1 := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hsummand t ht
  rw [hrepl]
  have hsplit :
      (∑ t ∈ Finset.Icc 1 n, if m ≤ t then F t else 1) =
        (∑ t ∈ Finset.Icc 1 n, if t < m then 1 else 0) +
        ∑ t ∈ Finset.Icc 1 n, if m ≤ t then F t else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hmt : m ≤ t
    · simp [hmt, not_lt.mpr hmt]
    · have htm : t < m := lt_of_not_ge hmt
      simp [hmt, htm]
  rw [hsplit]
  have hpre :
      (∑ t ∈ Finset.Icc 1 n, if t < m then (1 : ℝ) else 0) ≤ q := by
    have hsubset : (Finset.Icc 1 n).filter (fun t ↦ t < m) ⊆ Finset.Icc 1 q := by
      intro t ht
      rw [Finset.mem_filter] at ht
      rw [Finset.mem_Icc]
      exact ⟨(Finset.mem_Icc.mp ht.1).1, by omega⟩
    calc
      (∑ t ∈ Finset.Icc 1 n, if t < m then (1 : ℝ) else 0) =
          ((Finset.Icc 1 n).filter (fun t ↦ t < m)).card := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (Finset.Icc 1 q).card := by
        exact_mod_cast Finset.card_le_card hsubset
      _ = q := by simp
  have htail_eq :
      (∑ t ∈ Finset.Icc 1 n, if m ≤ t then F t else 0) =
        ∑ t ∈ Finset.Icc m n, F t := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext t
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor <;> intro ht
      · exact ⟨ht.2, ht.1.2⟩
      · exact ⟨⟨hm1.trans ht.1, ht.2⟩, ht.1⟩
    · intro t ht
      rfl
  rw [htail_eq]
  by_cases hmn : m ≤ n
  · rw [sum_Icc_eq_first_add_shift hmn]
    have hFm : F m ≤ 1 := by
      dsimp [F]
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg (ε * Real.sqrt (m : ℝ) - Real.sqrt (2 * a))]
    have hsumint := finite_tail_sum_le_integral hε ha hmn hum.le
    have hinterval_tail :
        (∫ x in (m : ℝ)..n,
          Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2)) ≤
        ∫ x : ℝ in Set.Ioi u,
          Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2) := by
      rw [intervalIntegral.integral_of_le (by exact_mod_cast hmn)]
      refine setIntegral_mono_set (μ := volume)
        (s := Set.Ioc (m : ℝ) n) (t := Set.Ioi u)
        (show IntegrableOn (fun x : ℝ ↦
          Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2))
          (Set.Ioi u) by simpa [u] using integrableOn_shifted_tail hε ha) ?_ ?_
      · filter_upwards with x
        exact (Real.exp_pos _).le
      · filter_upwards with x hx
        exact Set.mem_Ioi.mpr (hum.le.trans_lt (Set.mem_Ioc.mp hx).1)
    have htail :
        (∑ i ∈ Finset.Ico m n, F (i + 1)) ≤
          ∫ x : ℝ in Set.Ioi u,
            Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2) :=
      hsumint.trans hinterval_tail
    have hclosed :
        (∫ x : ℝ in Set.Ioi u,
          Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2)) =
          2 / ε ^ 2 * (1 + Real.sqrt (Real.pi * a)) := by
      simpa [u] using integral_shifted_tail_closed hε ha
    rw [hclosed] at htail
    calc
      (∑ t ∈ Finset.Icc 1 n, if t < m then (1 : ℝ) else 0) +
          (F m + ∑ i ∈ Finset.Ico m n, F (i + 1)) ≤
          (q : ℝ) + (1 + 2 / ε ^ 2 * (1 + Real.sqrt (Real.pi * a))) :=
        add_le_add hpre (add_le_add hFm htail)
      _ ≤ u + (1 + 2 / ε ^ 2 * (1 + Real.sqrt (Real.pi * a))) :=
        add_le_add hq le_rfl
      _ = 1 + 2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) := by
        dsimp [u]
        ring
  · have hempty : Finset.Icc m n = ∅ := by
      simp [Finset.Icc_eq_empty, Nat.lt_of_not_ge hmn]
    rw [hempty, Finset.sum_empty]
    have hnonneg : 0 ≤ 2 / ε ^ 2 * (1 + Real.sqrt (Real.pi * a)) := by positivity
    have hq_le : (q : ℝ) ≤ 1 + 2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) := by
      have hu_eq : u = 2 / ε ^ 2 * a := by
        dsimp [u]
        ring
      nlinarith [hq, hnonneg]
    simpa using hpre.trans hq_le
