-- Prove2me | solution 1 for EthierKurtz.kernel_potential_derivative_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T12:37:59.562383+00:00
-- url     : https://prove2.me/submissions/7d7ef8a2-ee35-4b0f-aa78-76f6f4b4f746

import Mathlib

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology

namespace ObliqueLib
/-- Euclidean space of dimension `d`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

lemma integrable_exp_sq {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : Eu d => rexp (-b * ‖v‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Eu d)
    (b := (b : ℂ)) (by simpa using hb) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun v => ?_)
  have : (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 + 0 * ((inner ℝ (0 : Eu d) v : ℝ) : ℂ))
      = ((-b * ‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  simp only [this, Complex.norm_exp_ofReal]

lemma integral_exp_sq {d : ℕ} {b : ℝ} (hb : 0 < b) :
    ∫ v : Eu d, rexp (-b * ‖v‖ ^ 2) = (π / b) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin]

/-- Normalized Gaussian of "variance parameter" `s`: `G s z = (π s)^(-d/2) exp(-|z|^2/s)`. -/
noncomputable def G (d : ℕ) (s : ℝ) (z : Eu d) : ℝ :=
  (π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s)

lemma G_pos {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 < G d s z :=
  mul_pos (rpow_pos_of_pos (mul_pos pi_pos hs) _) (exp_pos _)

lemma G_nonneg {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 ≤ G d s z := (G_pos hs z).le

lemma G_eq {d : ℕ} {s : ℝ} (z : Eu d) :
    G d s z = (π * s) ^ (-((d : ℝ) / 2)) * rexp (-(1 / s) * ‖z‖ ^ 2) := by
  rw [G]; congr 2; ring

lemma continuous_G {d : ℕ} (s : ℝ) : Continuous (G d s) := by
  unfold G; fun_prop

lemma integrable_G {d : ℕ} {s : ℝ} (hs : 0 < s) : Integrable (G d s) := by
  have h := (integrable_exp_sq (d := d) (b := 1 / s) (by positivity)).const_mul
    ((π * s) ^ (-((d : ℝ) / 2)))
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  rw [G_eq]

lemma integral_G {d : ℕ} {s : ℝ} (hs : 0 < s) : ∫ z, G d s z = 1 := by
  simp_rw [G_eq]
  rw [integral_const_mul, integral_exp_sq (by positivity)]
  have hps : 0 < π * s := mul_pos pi_pos hs
  rw [show π / (1 / s) = π * s by field_simp, rpow_neg hps.le]
  exact inv_mul_cancel₀ (rpow_pos_of_pos hps _).ne'

lemma pow_mul_exp_le (k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    a ^ k * rexp (-a) ≤ 2 ^ k * k.factorial * rexp (-a / 2) := by
  have h := Real.pow_div_factorial_le_exp (x := a / 2) (by positivity) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h1 : a ^ k ≤ 2 ^ k * k.factorial * rexp (a / 2) := by
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
    linarith
  calc a ^ k * rexp (-a) ≤ 2 ^ k * k.factorial * rexp (a / 2) * rexp (-a) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = 2 ^ k * k.factorial * rexp (-a / 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- `(|z|^2/s)^k G(s,z) ≤ 2^k k! 2^(d/2) G(2s,z)`. -/
lemma pow_mul_G_le {d : ℕ} (k : ℕ) {s : ℝ} (hs : 0 < s) (z : Eu d) :
    (‖z‖ ^ 2 / s) ^ k * G d s z ≤
      2 ^ k * k.factorial * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z := by
  have hps : 0 < π * s := mul_pos pi_pos hs
  have ha : 0 ≤ ‖z‖ ^ 2 / s := by positivity
  have h := pow_mul_exp_le k ha
  have e1 : (π * (2 * s)) ^ (-((d : ℝ) / 2)) =
      (2 : ℝ) ^ (-((d : ℝ) / 2)) * (π * s) ^ (-((d : ℝ) / 2)) := by
    rw [show π * (2 * s) = 2 * (π * s) by ring, mul_rpow (by norm_num) hps.le]
  have e2 : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-((d : ℝ) / 2)) = 1 := by
    rw [← rpow_add (by norm_num)]; simp
  have e3 : -(‖z‖ ^ 2 / s) / 2 = -‖z‖ ^ 2 / (2 * s) := by field_simp
  unfold G
  rw [e1, ← e3]
  have hP : 0 ≤ (π * s) ^ (-((d : ℝ) / 2)) := (rpow_pos_of_pos hps _).le
  calc (‖z‖ ^ 2 / s) ^ k * ((π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s))
      = (π * s) ^ (-((d : ℝ) / 2)) * ((‖z‖ ^ 2 / s) ^ k * rexp (-(‖z‖ ^ 2 / s))) := by
        rw [neg_div]; ring
    _ ≤ (π * s) ^ (-((d : ℝ) / 2)) * (2 ^ k * k.factorial * rexp (-(‖z‖ ^ 2 / s) / 2)) :=
        mul_le_mul_of_nonneg_left h hP
    _ = 2 ^ k * k.factorial * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-((d : ℝ) / 2))) *
          ((π * s) ^ (-((d : ℝ) / 2)) * rexp (-(‖z‖ ^ 2 / s) / 2)) := by
        rw [e2]; ring
    _ = 2 ^ k * k.factorial * 2 ^ ((d : ℝ) / 2) *
          ((2 : ℝ) ^ (-((d : ℝ) / 2)) * (π * s) ^ (-((d : ℝ) / 2)) *
            rexp (-(‖z‖ ^ 2 / s) / 2)) := by ring

/-- `|z|^μ ≤ s^(μ/2) (1 + |z|^2/s)` for `0 ≤ μ ≤ 2`. -/
lemma rpow_norm_le {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (z : Eu d) :
    ‖z‖ ^ μ ≤ s ^ (μ / 2) * (1 + ‖z‖ ^ 2 / s) := by
  set a := ‖z‖ ^ 2 / s with ha_def
  have ha : 0 ≤ a := by positivity
  have hz : ‖z‖ ^ μ = s ^ (μ / 2) * a ^ (μ / 2) := by
    rw [ha_def, div_rpow (by positivity) hs.le, ← rpow_natCast, ← rpow_mul (norm_nonneg _)]
    rw [mul_div_cancel₀ _ (rpow_pos_of_pos hs _).ne']
    congr 1; push_cast; ring
  rw [hz]
  refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg hs.le _)
  rcases le_total a 1 with h1 | h1
  · have := rpow_le_one ha h1 (by linarith : 0 ≤ μ / 2)
    linarith
  · have := rpow_le_rpow_of_exponent_le h1 (by linarith : μ / 2 ≤ 1)
    rw [rpow_one] at this
    linarith

/-- Gaussian moment constant. -/
noncomputable def gm (d : ℕ) : ℝ := 1 + 2 * 2 ^ ((d : ℝ) / 2)

lemma moment_bound_pt {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (z : Eu d) :
    G d s z * ‖z‖ ^ μ ≤ s ^ (μ / 2) * (G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z) := by
  have h1 := rpow_norm_le hs hμ0 hμ2 z
  have h2 := pow_mul_G_le 1 hs z
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at h2
  have hG := G_nonneg hs z
  have hsμ : 0 ≤ s ^ (μ / 2) := rpow_nonneg hs.le _
  calc G d s z * ‖z‖ ^ μ ≤ G d s z * (s ^ (μ / 2) * (1 + ‖z‖ ^ 2 / s)) :=
        mul_le_mul_of_nonneg_left h1 hG
    _ = s ^ (μ / 2) * (G d s z + ‖z‖ ^ 2 / s * G d s z) := by ring
    _ ≤ s ^ (μ / 2) * (G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z) := by
        gcongr

lemma integrable_G_mul_rpow {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) :
    Integrable (fun z : Eu d => G d s z * ‖z‖ ^ μ) := by
  have hI : Integrable (fun z : Eu d =>
      s ^ (μ / 2) * (G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z)) :=
    ((integrable_G hs).add ((integrable_G (by positivity)).const_mul _)).const_mul _
  refine hI.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact ((continuous_G s).mul (continuous_norm.rpow_const fun _ => Or.inr hμ0)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (G_nonneg hs z) (rpow_nonneg (norm_nonneg _) _))]
    exact moment_bound_pt hs hμ0 hμ2 z

lemma integral_G_mul_rpow_le {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) :
    ∫ z : Eu d, G d s z * ‖z‖ ^ μ ≤ gm d * s ^ (μ / 2) := by
  have hI2 : Integrable (fun z : Eu d => G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z) :=
    (integrable_G hs).add ((integrable_G (by positivity)).const_mul _)
  calc ∫ z : Eu d, G d s z * ‖z‖ ^ μ
      ≤ ∫ z : Eu d, s ^ (μ / 2) * (G d s z + 2 * 2 ^ ((d : ℝ) / 2) * G d (2 * s) z) :=
        integral_mono (integrable_G_mul_rpow hs hμ0 hμ2) (hI2.const_mul _)
          (fun z => moment_bound_pt hs hμ0 hμ2 z)
    _ = gm d * s ^ (μ / 2) := by
        rw [integral_const_mul, integral_add (integrable_G hs)
          ((integrable_G (by positivity)).const_mul _), integral_const_mul,
          integral_G hs, integral_G (by positivity), gm]
        ring

lemma integrable_G_sub {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Eu d) :
    Integrable (fun y : Eu d => G d s (x - y)) :=
  (integrable_G hs).comp_sub_left x

lemma integral_G_sub {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Eu d) :
    ∫ y : Eu d, G d s (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun z => G d s z) volume x, integral_G hs]

lemma integrable_G_sub_mul_rpow {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    (x : Eu d) : Integrable (fun y : Eu d => G d s (x - y) * ‖x - y‖ ^ μ) :=
  (integrable_G_mul_rpow hs hμ0 hμ2).comp_sub_left x

lemma integral_G_sub_mul_rpow_le {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    (x : Eu d) : ∫ y : Eu d, G d s (x - y) * ‖x - y‖ ^ μ ≤ gm d * s ^ (μ / 2) := by
  rw [integral_sub_left_eq_self (fun z => G d s z * ‖z‖ ^ μ) volume x]
  exact integral_G_mul_rpow_le hs hμ0 hμ2

/-- Shortcut instances: without them `Norm (E →L E →L E →L ℝ)` fails to synthesize. -/
noncomputable local instance instL2N (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section KHypDef

/-- Hypotheses on a kernel family `K t x y` (time `t > 0`) with `x`-derivatives `K1 K2 K3`
and Gaussian bounds on the convex set `S`. -/
@[reducible] def KHyp (d : ℕ) (S : Set (Eu d)) (K : ℝ → Eu d → Eu d → ℝ)
    (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ))
    (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)) (A c : ℝ) : Prop :=
  (0 ≤ A) ∧
    (0 < c) ∧
    (MeasurableSet S) ∧
    (Convex ℝ S) ∧
    (∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧
    (∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧
    (∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧
    (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G d (c * t) (x - y)) ∧
    (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G d (c * t) (x - y)) ∧
    (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G d (c * t) (x - y)) ∧
    (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K3 t x y‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * G d (c * t) (x - y)) ∧
    (∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K p.1 x p.2)) ∧
    (∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K1 p.1 x p.2)) ∧
    (∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K2 p.1 x p.2)) ∧
    (∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K3 p.1 x p.2)) ∧
    (∀ t, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, IntegrableOn F S ∧ ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧ ‖K3 t x y‖ ≤ F y) ∧
    (∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => K t x y) ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
    (∀ t, 0 < t → ∀ x, ∫ y in S, K t x y = 1)

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}

theorem KHyp.hA (h : KHyp d S K K1 K2 K3 A c) : 0 ≤ A := h.1

theorem KHyp.hc (h : KHyp d S K K1 K2 K3 A c) : 0 < c := h.2.1

theorem KHyp.hS (h : KHyp d S K K1 K2 K3 A c) : MeasurableSet S := h.2.2.1

theorem KHyp.hconv (h : KHyp d S K K1 K2 K3 A c) : Convex ℝ S := h.2.2.2.1

theorem KHyp.d1 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K t x y) (K1 t x y) x := h.2.2.2.2.1

theorem KHyp.d2 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K1 t x y) (K2 t x y) x := h.2.2.2.2.2.1

theorem KHyp.d3 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K2 t x y) (K3 t x y) x := h.2.2.2.2.2.2.1

theorem KHyp.b0 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.1

theorem KHyp.b1 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.1

theorem KHyp.b2 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.2.1

theorem KHyp.b3 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K3 t x y‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.2.2.1

theorem KHyp.m0 (h : KHyp d S K K1 K2 K3 A c) : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K p.1 x p.2) := h.2.2.2.2.2.2.2.2.2.2.2.1

theorem KHyp.m1 (h : KHyp d S K K1 K2 K3 A c) : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K1 p.1 x p.2) := h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem KHyp.m2 (h : KHyp d S K K1 K2 K3 A c) : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K2 p.1 x p.2) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem KHyp.m3 (h : KHyp d S K K1 K2 K3 A c) : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K3 p.1 x p.2) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem KHyp.dom (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, IntegrableOn F S ∧ ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧ ‖K3 t x y‖ ≤ F y := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem KHyp.mass (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x, ∫ y in S, K t x y = 1 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end KHypDef

/-- `h` is bounded by `M0` and `μ`-Hölder with constant `Hh` on `S`. -/
def HolderOnS {d : ℕ} (S : Set (Eu d)) (μ M0 Hh : ℝ) (h : Eu d → ℝ) : Prop :=
  0 ≤ M0 ∧ 0 ≤ Hh ∧ (∀ y ∈ S, |h y| ≤ M0) ∧ ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ

lemma integrableOn_G_sub {d : ℕ} {s : ℝ} (hs : 0 < s) (S : Set (Eu d)) (x : Eu d) :
    IntegrableOn (fun y : Eu d => G d s (x - y)) S :=
  (integrable_G_sub hs x).integrableOn

lemma setIntegral_G_sub_le {d : ℕ} {s : ℝ} (hs : 0 < s) (S : Set (Eu d)) (x : Eu d) :
    ∫ y in S, G d s (x - y) ≤ 1 := by
  calc ∫ y in S, G d s (x - y) ≤ ∫ y, G d s (x - y) :=
        setIntegral_le_integral (integrable_G_sub hs x)
          (Eventually.of_forall fun y => G_nonneg hs _)
    _ = 1 := integral_G_sub hs x

lemma setIntegral_G_sub_mul_rpow_le {d : ℕ} {s μ : ℝ} (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    (S : Set (Eu d)) (x : Eu d) :
    ∫ y in S, G d s (x - y) * ‖x - y‖ ^ μ ≤ gm d * s ^ (μ / 2) := by
  calc ∫ y in S, G d s (x - y) * ‖x - y‖ ^ μ ≤ ∫ y, G d s (x - y) * ‖x - y‖ ^ μ :=
        setIntegral_le_integral (integrable_G_sub_mul_rpow hs hμ0 hμ2 x)
          (Eventually.of_forall fun y =>
            mul_nonneg (G_nonneg hs _) (rpow_nonneg (norm_nonneg _) _))
    _ ≤ gm d * s ^ (μ / 2) := integral_G_sub_mul_rpow_le hs hμ0 hμ2 x

/-- Sup bound: `‖∫_S f • L‖ ≤ B M` when `‖L y‖ ≤ B G(s, x - y)` and `|f| ≤ M` on `S`. -/
lemma sup_bound {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {S : Set (Eu d)} (hS : MeasurableSet S) {L : Eu d → F'} {f : Eu d → ℝ} {x : Eu d}
    {B s M : ℝ} (hs : 0 < s) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hL : AEStronglyMeasurable L (volume.restrict S))
    (hf : AEStronglyMeasurable f (volume.restrict S))
    (hLb : ∀ y ∈ S, ‖L y‖ ≤ B * G d s (x - y)) (hfb : ∀ y ∈ S, |f y| ≤ M) :
    Integrable (fun y => f y • L y) (volume.restrict S) ∧
      ‖∫ y in S, f y • L y‖ ≤ B * M := by
  have hI : Integrable (fun y => M * B * G d s (x - y)) (volume.restrict S) :=
    (integrableOn_G_sub hs S x).const_mul (M * B)
  have hpt : ∀ᵐ y ∂(volume.restrict S), ‖f y • L y‖ ≤ M * B * G d s (x - y) :=
    (ae_restrict_iff' hS).mpr (Eventually.of_forall fun y hy => by
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul (hfb y hy) (hLb y hy) (norm_nonneg _) hM)
  refine ⟨hI.mono' (hf.smul hL) hpt, ?_⟩
  calc ‖∫ y in S, f y • L y‖ ≤ ∫ y in S, M * B * G d s (x - y) := norm_integral_le_of_norm_le hI hpt
    _ = M * B * ∫ y in S, G d s (x - y) := integral_const_mul _ _
    _ ≤ M * B * 1 := mul_le_mul_of_nonneg_left (setIntegral_G_sub_le hs S x) (by positivity)
    _ = B * M := by ring

/-- Zero-mean bound: `‖∫_S (h y - h x) • L y‖ ≤ B Hh gm s^(μ/2)`. -/
lemma zm_bound {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {S : Set (Eu d)} (hS : MeasurableSet S) {L : Eu d → F'} {h : Eu d → ℝ} {x : Eu d}
    {B s Hh μ : ℝ} (hs : 0 < s) (hB : 0 ≤ B) (hHh : 0 ≤ Hh) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    (hL : AEStronglyMeasurable L (volume.restrict S))
    (hhm : AEStronglyMeasurable h (volume.restrict S))
    (hLb : ∀ y ∈ S, ‖L y‖ ≤ B * G d s (x - y))
    (hH : ∀ y ∈ S, |h y - h x| ≤ Hh * ‖x - y‖ ^ μ) :
    Integrable (fun y => (h y - h x) • L y) (volume.restrict S) ∧
      ‖∫ y in S, (h y - h x) • L y‖ ≤ B * Hh * (gm d * s ^ (μ / 2)) := by
  have hI : Integrable (fun y => B * Hh * (G d s (x - y) * ‖x - y‖ ^ μ)) (volume.restrict S) :=
    ((integrable_G_sub_mul_rpow hs hμ0 hμ2 x).integrableOn).const_mul (B * Hh)
  have hpt : ∀ᵐ y ∂(volume.restrict S),
      ‖(h y - h x) • L y‖ ≤ B * Hh * (G d s (x - y) * ‖x - y‖ ^ μ) :=
    (ae_restrict_iff' hS).mpr (Eventually.of_forall fun y hy => by
      rw [norm_smul, Real.norm_eq_abs]
      calc |h y - h x| * ‖L y‖ ≤ (Hh * ‖x - y‖ ^ μ) * (B * G d s (x - y)) :=
            mul_le_mul (hH y hy) (hLb y hy) (norm_nonneg _)
              (mul_nonneg hHh (rpow_nonneg (norm_nonneg _) _))
        _ = B * Hh * (G d s (x - y) * ‖x - y‖ ^ μ) := by ring)
  refine ⟨hI.mono' ((hhm.sub aestronglyMeasurable_const).smul hL) hpt, ?_⟩
  calc ‖∫ y in S, (h y - h x) • L y‖
      ≤ ∫ y in S, B * Hh * (G d s (x - y) * ‖x - y‖ ^ μ) := norm_integral_le_of_norm_le hI hpt
    _ = B * Hh * ∫ y in S, G d s (x - y) * ‖x - y‖ ^ μ := integral_const_mul _ _
    _ ≤ B * Hh * (gm d * s ^ (μ / 2)) :=
        mul_le_mul_of_nonneg_left (setIntegral_G_sub_mul_rpow_le hs hμ0 hμ2 S x)
          (mul_nonneg hB hHh)

/-- Differentiation under `∫_S` of `x ↦ ∫_S h y • L x y` with a local integrable bound. -/
lemma hasFDerivAt_kint {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] {S : Set (Eu d)} (hS : MeasurableSet S) {L : Eu d → Eu d → F'}
    {L' : Eu d → Eu d → (Eu d →L[ℝ] F')} {h : Eu d → ℝ} {M0 : ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0)
    (hLm : ∀ x, AEStronglyMeasurable (L x) (volume.restrict S))
    (hL'm : ∀ x, AEStronglyMeasurable (L' x) (volume.restrict S))
    (hd : ∀ x y, HasFDerivAt (fun x => L x y) (L' x y) x)
    {x₀ : Eu d} {r : ℝ} (hr : 0 < r) {F : Eu d → ℝ} (hF : IntegrableOn F S)
    (hLb : ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, ‖L x y‖ ≤ F y)
    (hL'b : ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, ‖L' x y‖ ≤ F y) :
    HasFDerivAt (fun x => ∫ y in S, h y • L x y) (∫ y in S, h y • L' x₀ y) x₀ := by
  have hM0 : ∀ y ∈ S, 0 ≤ M0 := fun y hy => (abs_nonneg _).trans (hhb y hy)
  have hFint : Integrable (fun y => M0 * F y) (volume.restrict S) := hF.const_mul M0
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x y => h y • L x y)
    (F' := fun x y => h y • L' x y) (Metric.ball_mem_nhds x₀ hr)
    (Eventually.of_forall fun x => hh.smul (hLm x)) ?_ (hh.smul (hL'm x₀)) ?_ hFint ?_
  · refine hFint.mono' (hh.smul (hLm x₀)) ((ae_restrict_iff' hS).mpr
      (Eventually.of_forall fun y hy => ?_))
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hhb y hy) (hLb x₀ (Metric.mem_ball_self hr) y hy) (norm_nonneg _) (hM0 y hy)
  · refine (ae_restrict_iff' hS).mpr (Eventually.of_forall fun y hy x hx => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hhb y hy) (hL'b x hx y hy) (norm_nonneg _) (hM0 y hy)
  · exact Eventually.of_forall fun y x _ => (hd x y).const_smul (h y)

lemma zm_rewrite {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] {S : Set (Eu d)} {L : Eu d → F'} {h : Eu d → ℝ} (x : Eu d)
    (hL : Integrable L (volume.restrict S))
    (hhL : Integrable (fun y => h y • L y) (volume.restrict S))
    (h0 : ∫ y in S, L y = 0) :
    ∫ y in S, h y • L y = ∫ y in S, (h y - h x) • L y := by
  have hL2 : Integrable (fun y => h x • L y) (volume.restrict S) := hL.smul (h x)
  simp_rw [sub_smul]
  rw [integral_sub hhL hL2, integral_smul, h0, smul_zero, sub_zero]

/-- Generic Hölder (zero-mean) bound for `∫_S h • L` with a Gaussian-bounded, mean-zero `L`. -/
lemma kint_hol_bound {d : ℕ} {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] {S : Set (Eu d)} (hS : MeasurableSet S) {L : Eu d → F'}
    {h : Eu d → ℝ} {x : Eu d} (hx : x ∈ S) {B s μ M0 Hh : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S))
    (hLm : AEStronglyMeasurable L (volume.restrict S))
    (hLb : ∀ y ∈ S, ‖L y‖ ≤ B * G d s (x - y)) (h0 : ∫ y in S, L y = 0) :
    ‖∫ y in S, h y • L y‖ ≤ B * Hh * (gm d * s ^ (μ / 2)) := by
  obtain ⟨hM0, hHh, hb, hH⟩ := hhol
  have hLi : Integrable L (volume.restrict S) :=
    ((integrableOn_G_sub hs S x).const_mul B).mono' hLm
      ((ae_restrict_iff' hS).mpr (Eventually.of_forall fun y hy => hLb y hy))
  have hhL := (sup_bound hS hs hB hM0 hLm hh hLb hb).1
  rw [zm_rewrite x hLi hhL h0]
  refine (zm_bound hS hs hB hHh hμ0 hμ2 hLm hh hLb fun y hy => ?_).2
  rw [norm_sub_rev]; exact hH y hy x hx

section C1Hdef

/-- `ψ` is bounded, differentiable with bounded, continuous, `μ`-Hölder derivative `ψ1`. -/
@[reducible] def C1H (d : ℕ) (μ M0 M1 H : ℝ) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) : Prop :=
  (∀ y, HasFDerivAt ψ (ψ1 y) y) ∧ Continuous ψ1 ∧ (∀ y, |ψ y| ≤ M0) ∧ (∀ y, ‖ψ1 y‖ ≤ M1) ∧
    (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H

variable {d : ℕ} {μ M0 M1 H : ℝ} {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)}

theorem C1H.hd (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, HasFDerivAt ψ (ψ1 y) y := hC.1

theorem C1H.b0 (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, |ψ y| ≤ M0 := hC.2.2.1

theorem C1H.b1 (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, ‖ψ1 y‖ ≤ M1 := hC.2.2.2.1

theorem C1H.hH (hC : C1H d μ M0 M1 H ψ ψ1) : 0 ≤ H := hC.2.2.2.2.2

end C1Hdef

section KernelInt

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}

lemma KHyp.sm0 (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d) :
    StronglyMeasurable (fun y => K t x y) :=
  (KH.m0 x).comp_measurable measurable_prodMk_left

lemma KHyp.sm1 (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d) :
    StronglyMeasurable (fun y => K1 t x y) :=
  (KH.m1 x).comp_measurable measurable_prodMk_left

lemma KHyp.sm2 (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d) :
    StronglyMeasurable (fun y => K2 t x y) :=
  (KH.m2 x).comp_measurable measurable_prodMk_left

lemma KHyp.sm3 (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d) :
    StronglyMeasurable (fun y => K3 t x y) :=
  (KH.m3 x).comp_measurable measurable_prodMk_left

/-- Space integrals of the kernel and its derivatives against `h`. -/
noncomputable def kw0 (S : Set (Eu d)) (K : ℝ → Eu d → Eu d → ℝ) (h : Eu d → ℝ) (t : ℝ)
    (x : Eu d) : ℝ := ∫ y in S, h y • K t x y

noncomputable def kw1 (S : Set (Eu d)) (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)) (h : Eu d → ℝ)
    (t : ℝ) (x : Eu d) : Eu d →L[ℝ] ℝ := ∫ y in S, h y • K1 t x y

noncomputable def kw2 (S : Set (Eu d)) (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (h : Eu d → ℝ) (t : ℝ) (x : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ := ∫ y in S, h y • K2 t x y

noncomputable def kw3 (S : Set (Eu d))
    (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (h : Eu d → ℝ) (t : ℝ) (x : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ y in S, h y • K3 t x y

variable {h : Eu d → ℝ} {M0 : ℝ}

lemma KHyp.hasFDerivAt_kw0 (KH : KHyp d S K K1 K2 K3 A c)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0)
    {t : ℝ} (ht : 0 < t) (x : Eu d) : HasFDerivAt (kw0 S K h t) (kw1 S K1 h t x) x := by
  obtain ⟨r, hr, F, hF, hb⟩ := KH.dom t ht x
  unfold kw0 kw1
  exact hasFDerivAt_kint KH.hS hh hhb (fun x => (KH.sm0 t x).aestronglyMeasurable)
    (fun x => (KH.sm1 t x).aestronglyMeasurable) (KH.d1 t ht) hr hF
    (fun x hx y hy => by rw [Real.norm_eq_abs]; exact (hb x hx y hy).1)
    (fun x hx y hy => (hb x hx y hy).2.1)

lemma KHyp.hasFDerivAt_kw1 (KH : KHyp d S K K1 K2 K3 A c)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0)
    {t : ℝ} (ht : 0 < t) (x : Eu d) : HasFDerivAt (kw1 S K1 h t) (kw2 S K2 h t x) x := by
  obtain ⟨r, hr, F, hF, hb⟩ := KH.dom t ht x
  unfold kw1 kw2
  exact hasFDerivAt_kint KH.hS hh hhb (fun x => (KH.sm1 t x).aestronglyMeasurable)
    (fun x => (KH.sm2 t x).aestronglyMeasurable) (KH.d2 t ht) hr hF
    (fun x hx y hy => (hb x hx y hy).2.1) (fun x hx y hy => (hb x hx y hy).2.2.1)

lemma KHyp.hasFDerivAt_kw2 (KH : KHyp d S K K1 K2 K3 A c)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0)
    {t : ℝ} (ht : 0 < t) (x : Eu d) : HasFDerivAt (kw2 S K2 h t) (kw3 S K3 h t x) x := by
  obtain ⟨r, hr, F, hF, hb⟩ := KH.dom t ht x
  unfold kw2 kw3
  exact hasFDerivAt_kint KH.hS hh hhb (fun x => (KH.sm2 t x).aestronglyMeasurable)
    (fun x => (KH.sm3 t x).aestronglyMeasurable) (KH.d3 t ht) hr hF
    (fun x hx y hy => (hb x hx y hy).2.2.1) (fun x hx y hy => (hb x hx y hy).2.2.2)

/-- Zero mean of the first derivative kernel. -/
lemma KHyp.int_K1 (KH : KHyp d S K K1 K2 K3 A c) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    ∫ y in S, K1 t x y = 0 := by
  have h1 := KH.hasFDerivAt_kw0 (h := fun _ => 1) (M0 := 1) aestronglyMeasurable_const
    (fun _ _ => by simp) ht x
  have hc : kw0 S K (fun _ => 1) t = fun _ => 1 := by
    funext z; simp only [kw0, one_smul]; exact KH.mass t ht z
  rw [hc] at h1
  have := h1.unique (hasFDerivAt_const (1 : ℝ) x)
  simpa [kw1] using this

lemma KHyp.int_K2 (KH : KHyp d S K K1 K2 K3 A c) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    ∫ y in S, K2 t x y = 0 := by
  have h1 := KH.hasFDerivAt_kw1 (h := fun _ => 1) (M0 := 1) aestronglyMeasurable_const
    (fun _ _ => by simp) ht x
  have hc : kw1 S K1 (fun _ => 1) t = fun _ => 0 := by
    funext z; simp only [kw1, one_smul]; exact KH.int_K1 ht z
  rw [hc] at h1
  have := h1.unique (hasFDerivAt_const (0 : Eu d →L[ℝ] ℝ) x)
  simpa [kw2] using this

lemma KHyp.int_K3 (KH : KHyp d S K K1 K2 K3 A c) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    ∫ y in S, K3 t x y = 0 := by
  have h1 := KH.hasFDerivAt_kw2 (h := fun _ => 1) (M0 := 1) aestronglyMeasurable_const
    (fun _ _ => by simp) ht x
  have hc : kw2 S K2 (fun _ => 1) t = fun _ => 0 := by
    funext z; simp only [kw2, one_smul]; exact KH.int_K2 ht z
  rw [hc] at h1
  have := h1.unique (hasFDerivAt_const (0 : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) x)
  simpa [kw3] using this

end KernelInt

section KernelBounds

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

lemma KHyp.kw0_le (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ S) : |kw0 S K h t x| ≤ A * M0 := by
  have := (sup_bound KH.hS (mul_pos KH.hc ht) KH.hA hhol.1 (KH.sm0 t x).aestronglyMeasurable hh
    (fun y hy => by rw [Real.norm_eq_abs]; exact KH.b0 t ht x hx y hy) hhol.2.2.1).2
  rwa [Real.norm_eq_abs] at this

lemma KHyp.kw1_le (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ S) : ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * M0 :=
  (sup_bound KH.hS (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _)) hhol.1
    (KH.sm1 t x).aestronglyMeasurable hh (fun y hy => KH.b1 t ht x hx y hy) hhol.2.2.1).2

lemma KHyp.kw2_le (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ S) : ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * M0 :=
  (sup_bound KH.hS (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _)) hhol.1
    (KH.sm2 t x).aestronglyMeasurable hh (fun y hy => KH.b2 t ht x hx y hy) hhol.2.2.1).2

lemma KHyp.kw1_hol (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S) :
    ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) :=
  kint_hol_bound KH.hS hx (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _)) hμ0 hμ2
    hhol hh (KH.sm1 t x).aestronglyMeasurable (fun y hy => KH.b1 t ht x hx y hy) (KH.int_K1 ht x)

lemma KHyp.kw2_hol (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S) :
    ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) :=
  kint_hol_bound KH.hS hx (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _)) hμ0 hμ2
    hhol hh (KH.sm2 t x).aestronglyMeasurable (fun y hy => KH.b2 t ht x hx y hy) (KH.int_K2 ht x)

lemma KHyp.kw3_hol (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S) :
    ‖kw3 S K3 h t x‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) :=
  kint_hol_bound KH.hS hx (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _)) hμ0 hμ2
    hhol hh (KH.sm3 t x).aestronglyMeasurable (fun y hy => KH.b3 t ht x hx y hy) (KH.int_K3 ht x)

end KernelBounds

section TimeK

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

lemma KHyp.tm2 (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S))
    (x : Eu d) : AEStronglyMeasurable (fun t => kw2 S K2 h t x) (volume.restrict (Ioi 0)) := by
  unfold kw2
  exact AEStronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × Eu d => h p.2 • K2 p.1 x p.2)
    (hh.comp_snd.smul (KH.m2 x).aestronglyMeasurable)

lemma KHyp.kw1_lip (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x x' : Eu d}
    (hx : x ∈ S) (hx' : x' ∈ S) :
    ‖kw1 S K1 h t x - kw1 S K1 h t x'‖ ≤ A * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (KH.hasFDerivAt_kw1 hh hhol.2.2.1 ht z).hasFDerivWithinAt)
    (fun z hz => KH.kw2_le hhol hh ht hz) KH.hconv hx' hx

variable {lam : ℝ}

end TimeK

section TimeHol

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

end TimeHol

end ObliqueLib

open ObliqueLib in
theorem solution :
∀ (d : ℕ),
  letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
  letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
  letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
  letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
  letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
  letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
  letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
  letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
  letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
  letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
  letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
  letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
  letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
  letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
  letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
  letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
  let G : (s : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s));
  let gm : ℝ := (1 + 2 * 2 ^ ((d : ℝ) / 2));
  let KHyp : (S : Set (EuclideanSpace ℝ (Fin d))) → (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) → (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (A c : ℝ) → Prop := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (A c : ℝ) => ((0 ≤ A) ∧ (0 < c) ∧ (MeasurableSet S) ∧ (Convex ℝ S) ∧ (∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧ (∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧ (∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧ (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G (c * t) (x - y)) ∧ (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G (c * t) (x - y)) ∧ (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G (c * t) (x - y)) ∧ (∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K3 t x y‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * G (c * t) (x - y)) ∧ (∀ x, StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K p.1 x p.2)) ∧ (∀ x, StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K1 p.1 x p.2)) ∧ (∀ x, StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K2 p.1 x p.2)) ∧ (∀ x, StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K3 p.1 x p.2)) ∧ (∀ t, 0 < t → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, IntegrableOn F S ∧ ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧ ‖K3 t x y‖ ≤ F y) ∧ (∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => K t x y) ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧ (∀ t, 0 < t → ∀ x, ∫ y in S, K t x y = 1));
  let HolderOnS : {d : ℕ} → (S : Set (EuclideanSpace ℝ (Fin d))) → (μ M0 Hh : ℝ) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → Prop := fun {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (μ M0 Hh : ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) => (0 ≤ M0 ∧ 0 ≤ Hh ∧ (∀ y ∈ S, |h y| ≤ M0) ∧ ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ);
  let kw0 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K t x y);
  let kw1 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K1 t x y);
  let kw2 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K2 t x y);
  let kw3 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K3 t x y);
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} (KH : KHyp S K K1 K2 K3 A c) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), StronglyMeasurable (fun y => K t x y)) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} (KH : KHyp S K K1 K2 K3 A c) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), StronglyMeasurable (fun y => K2 t x y)) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {M0 : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), HasFDerivAt (kw0 S K h t) (kw1 S K1 h t x) x) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {M0 : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), HasFDerivAt (kw1 S K1 h t) (kw2 S K2 h t x) x) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {M0 : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), HasFDerivAt (kw2 S K2 h t) (kw3 S K3 h t x) x) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S), |kw0 S K h t x| ≤ A * M0) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S), ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * M0) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S), ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * M0) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S), ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * Hh * (gm * (c * t) ^ (μ / 2))) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S), ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * Hh * (gm * (c * t) ^ (μ / 2))) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S), ‖kw3 S K3 h t x‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * Hh * (gm * (c * t) ^ (μ / 2))) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} (KH : KHyp S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (x : EuclideanSpace ℝ (Fin d)), AEStronglyMeasurable (fun t => kw2 S K2 h t x) (volume.restrict (Ioi 0))) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x x' : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S) (hx' : x' ∈ S), ‖kw1 S K1 h t x - kw1 S K1 h t x'‖ ≤ A * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖) := by
  intro d
  intro G gm KHyp HolderOnS kw0 kw1 kw2 kw3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S K K1 K2 K3 A c KH t x; exact ObliqueLib.KHyp.sm0 KH t x
  · intro S K K1 K2 K3 A c KH t x; exact ObliqueLib.KHyp.sm2 KH t x
  · intro S K K1 K2 K3 A c h M0 KH hh hhb t ht x; exact ObliqueLib.KHyp.hasFDerivAt_kw0 KH hh hhb ht x
  · intro S K K1 K2 K3 A c h M0 KH hh hhb t ht x; exact ObliqueLib.KHyp.hasFDerivAt_kw1 KH hh hhb ht x
  · intro S K K1 K2 K3 A c h M0 KH hh hhb t ht x; exact ObliqueLib.KHyp.hasFDerivAt_kw2 KH hh hhb ht x
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh t ht x hx; exact ObliqueLib.KHyp.kw0_le KH hhol hh ht hx
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh t ht x hx; exact ObliqueLib.KHyp.kw1_le KH hhol hh ht hx
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh t ht x hx; exact ObliqueLib.KHyp.kw2_le KH hhol hh ht hx
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh hμ0 hμ2 t ht x hx; exact ObliqueLib.KHyp.kw1_hol KH hhol hh hμ0 hμ2 ht hx
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh hμ0 hμ2 t ht x hx; exact ObliqueLib.KHyp.kw2_hol KH hhol hh hμ0 hμ2 ht hx
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh hμ0 hμ2 t ht x hx; exact ObliqueLib.KHyp.kw3_hol KH hhol hh hμ0 hμ2 ht hx
  · intro S K K1 K2 K3 A c h KH hh x; exact ObliqueLib.KHyp.tm2 KH hh x
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh t ht x x' hx hx'; exact ObliqueLib.KHyp.kw1_lip KH hhol hh ht hx hx'
