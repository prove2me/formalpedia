-- Prove2me | solution 1 for EthierKurtz.kernel_potential_time_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T13:26:29.678265+00:00
-- url     : https://prove2.me/submissions/99f27875-2e03-4a75-ac07-08898d3203ce

import Mathlib
import Theorems.Thm_EthierKurtz_kernel_potential_derivative_estimates

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

lemma gm_pos (d : ℕ) : 0 < gm d := by unfold gm; positivity

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

theorem KHyp.b0 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.1

theorem KHyp.b2 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.2.1

theorem KHyp.m3 (h : KHyp d S K K1 K2 K3 A c) : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K3 p.1 x p.2) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem KHyp.heat (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => K t x y) ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

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

/-- Trace of a bilinear form in the standard basis (twice the generator `Δ/2` acts as `lap2/2`). -/
noncomputable def lap2 {d : ℕ} (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : ℝ :=
  ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

lemma continuous_lap2 {d : ℕ} : Continuous (lap2 (d := d)) := by
  unfold lap2; fun_prop

lemma abs_lap2_le {d : ℕ} (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : |lap2 B| ≤ d * ‖B‖ := by
  unfold lap2
  calc |∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)|
      ≤ ∑ i : Fin d, |B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖B‖ := Finset.sum_le_sum fun i _ => by
        have := B.le_opNorm₂ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i 1)
        rw [EuclideanSpace.norm_single, norm_one, mul_one, mul_one] at this
        rwa [← Real.norm_eq_abs]
    _ = d * ‖B‖ := by simp

lemma lap2_smul {d : ℕ} (a : ℝ) (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : lap2 (a • B) = a * lap2 B := by
  unfold lap2; rw [Finset.mul_sum]; rfl

lemma lap2_integral {d : ℕ} {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {φ : α → Eu d →L[ℝ] Eu d →L[ℝ] ℝ} (hφ : Integrable φ ν) :
    lap2 (∫ a, φ a ∂ν) = ∫ a, lap2 (φ a) ∂ν := by
  unfold lap2
  rw [integral_finsetSum _ fun i _ =>
    (hφ.apply_continuousLinearMap _).apply_continuousLinearMap _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.integral_apply hφ, ContinuousLinearMap.integral_apply
    (hφ.apply_continuousLinearMap _)]

/-- Local comparison of Gaussians with nearby parameters. -/
lemma G_le_near {d : ℕ} {s s' : ℝ} (hs : 0 < s) (h1 : s / 2 ≤ s') (h2 : s' ≤ 2 * s) (z : Eu d) :
    G d s' z ≤ (4 : ℝ) ^ ((d : ℝ) / 2) * G d (2 * s) z := by
  unfold G
  have hs' : 0 < s' := by linarith
  have e1 : (π * s') ^ (-((d : ℝ) / 2)) ≤ (4 : ℝ) ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) := by
    calc (π * s') ^ (-((d : ℝ) / 2)) ≤ (π * (2 * s) / 4) ^ (-((d : ℝ) / 2)) :=
          rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [pi_pos]) (by
            have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      _ = (4 : ℝ) ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) := by
          rw [div_rpow (by positivity) (by norm_num), rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
          field_simp
  have e2 : rexp (-‖z‖ ^ 2 / s') ≤ rexp (-‖z‖ ^ 2 / (2 * s)) := by
    apply exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  calc (π * s') ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s')
      ≤ ((4 : ℝ) ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2))) * rexp (-‖z‖ ^ 2 / (2 * s)) :=
        mul_le_mul e1 e2 (exp_pos _).le (by positivity)
    _ = _ := by ring

section C1Hdef

/-- `ψ` is bounded, differentiable with bounded, continuous, `μ`-Hölder derivative `ψ1`. -/
@[reducible] def C1H (d : ℕ) (μ M0 M1 H : ℝ) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) : Prop :=
  (∀ y, HasFDerivAt ψ (ψ1 y) y) ∧ Continuous ψ1 ∧ (∀ y, |ψ y| ≤ M0) ∧ (∀ y, ‖ψ1 y‖ ≤ M1) ∧
    (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H

variable {d : ℕ} {μ M0 M1 H : ℝ} {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)}

theorem C1H.hd (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, HasFDerivAt ψ (ψ1 y) y := hC.1

theorem C1H.b0 (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, |ψ y| ≤ M0 := hC.2.2.1

theorem C1H.hH (hC : C1H d μ M0 M1 H ψ ψ1) : 0 ≤ H := hC.2.2.2.2.2

end C1Hdef

section KernelInt

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}

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

end KernelInt

section KernelBounds

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

end KernelBounds

section TimeK

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

variable {lam : ℝ}

end TimeK

section TimeHol

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

end TimeHol

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  KHyp_sm0 : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d), StronglyMeasurable (fun y => K t x y)
  KHyp_sm2 : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d), StronglyMeasurable (fun y => K2 t x y)
  KHyp_hasFDerivAt_kw0 : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw0 S K h t) (kw1 S K1 h t x) x
  KHyp_hasFDerivAt_kw2 : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw2 S K2 h t) (kw3 S K3 h t x) x
  KHyp_kw2_le : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * M0
  KHyp_kw3_hol : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw3 S K3 h t x‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2))
  KHyp_tm2 : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (x : Eu d), AEStronglyMeasurable (fun t => kw2 S K2 h t x) (volume.restrict (Ioi 0))

end IFk

theorem KHyp.sm0 {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d), StronglyMeasurable (fun y => K t x y) := IFacts.KHyp_sm0

theorem KHyp.sm2 {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (t : ℝ) (x : Eu d), StronglyMeasurable (fun y => K2 t x y) := IFacts.KHyp_sm2

theorem KHyp.hasFDerivAt_kw0 {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw0 S K h t) (kw1 S K1 h t x) x := IFacts.KHyp_hasFDerivAt_kw0

theorem KHyp.hasFDerivAt_kw2 {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw2 S K2 h t) (kw3 S K3 h t x) x := IFacts.KHyp_hasFDerivAt_kw2

theorem KHyp.kw2_le {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * M0 := IFacts.KHyp_kw2_le

theorem KHyp.kw3_hol {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw3 S K3 h t x‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) := IFacts.KHyp_kw3_hol

theorem KHyp.tm2 {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (x : Eu d), AEStronglyMeasurable (fun t => kw2 S K2 h t x) (volume.restrict (Ioi 0)) := IFacts.KHyp_tm2

section TimeDeriv

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

variable [IFacts d]

/-- `kw0 t x → h x`: quantitative form. -/
lemma KHyp.kw0_sub_h (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S) :
    |kw0 S K h t x - h x| ≤ A * Hh * (gm d * (c * t) ^ (μ / 2)) := by
  have hb : ∀ y ∈ S, ‖K t x y‖ ≤ A * G d (c * t) (x - y) := fun y hy => by
    rw [Real.norm_eq_abs]; exact KH.b0 t ht x hx y hy
  have hLm := (KH.sm0 t x).aestronglyMeasurable (μ := volume.restrict S)
  have hLi : Integrable (fun y => K t x y) (volume.restrict S) :=
    ((integrableOn_G_sub (mul_pos KH.hc ht) S x).const_mul A).mono' hLm
      ((ae_restrict_iff' KH.hS).mpr (Eventually.of_forall fun y hy => hb y hy))
  have hhL := (sup_bound KH.hS (mul_pos KH.hc ht) KH.hA hhol.1 hLm hh hb hhol.2.2.1).1
  have he : kw0 S K h t x - h x = ∫ y in S, (h y - h x) • K t x y := by
    unfold kw0
    simp_rw [sub_smul]
    have hLi' : Integrable (fun y => h x • K t x y) (volume.restrict S) := hLi.smul (h x)
    rw [integral_sub hhL hLi', integral_smul, KH.mass t ht x, smul_eq_mul, mul_one]
  rw [he, ← Real.norm_eq_abs]
  exact (zm_bound KH.hS (mul_pos KH.hc ht) KH.hA hhol.2.1 hμ0 hμ2 hLm hh hb fun y hy => by
    rw [norm_sub_rev]; exact hhol.2.2.2 y hy x hx).2

/-- Heat equation for the space integral: `∂_t kw0 = lap2 (kw2) / 2` on `S`. -/
lemma KHyp.hasDerivAt_kw0_t (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ S) :
    HasDerivAt (fun t => kw0 S K h t x) ((1 / 2 : ℝ) * lap2 (kw2 S K2 h t x)) t := by
  have hc := KH.hc
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set C := M0 * (1 / 2) * d * A * (2 / t) * (4 : ℝ) ^ ((d : ℝ) / 2) with hC
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict S)
    (F := fun t y => h y * K t x y) (x₀ := t)
    (F' := fun t y => h y * ((1 / 2 : ℝ) * lap2 (K2 t x y)))
    (bound := fun y => C * G d (2 * (c * t)) (x - y)) (Ioo_mem_nhds (half_lt_self ht)
      (by linarith : t < 2 * t))
    (Eventually.of_forall fun t' => hh.mul (KH.sm0 t' x).aestronglyMeasurable)
    (sup_bound KH.hS (mul_pos KH.hc ht) KH.hA hhol.1 (KH.sm0 t x).aestronglyMeasurable hh
      (fun y hy => by rw [Real.norm_eq_abs]; exact KH.b0 t ht x hx y hy) hhol.2.2.1).1
    (hh.mul (aestronglyMeasurable_const.mul
      (continuous_lap2.comp_aestronglyMeasurable (KH.sm2 t x).aestronglyMeasurable)))
    ?_ ((integrableOn_G_sub (by positivity) S x).const_mul C) ?_
  · show HasDerivAt (fun n => ∫ y in S, h y * K n x y) _ t
    have hI2 := (sup_bound KH.hS (mul_pos KH.hc ht) (mul_nonneg KH.hA (rpow_nonneg ht.le _))
      hhol.1 (KH.sm2 t x).aestronglyMeasurable hh (fun y hy => KH.b2 t ht x hx y hy)
      hhol.2.2.1).1
    have e : ∫ y in S, h y * ((1 / 2 : ℝ) * lap2 (K2 t x y)) = (1 / 2 : ℝ) * lap2 (kw2 S K2 h t x) := by
      unfold kw2
      rw [lap2_integral hI2, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [lap2_smul]; ring
    rw [← e]
    exact key.2
  · refine (ae_restrict_iff' KH.hS).mpr (Eventually.of_forall fun y hy t' ht' => ?_)
    have ht'0 : 0 < t' := by linarith [ht'.1, half_pos ht]
    have hG := G_le_near (d := d) (mul_pos hc ht) (s' := c * t') (by nlinarith [ht'.1])
      (by nlinarith [ht'.2]) (x - y)
    have hK2 := KH.b2 t' ht'0 x hx y hy
    have hinv : t' ^ (-(1 : ℝ)) ≤ 2 / t := by
      rw [rpow_neg_one, inv_le_comm₀ ht'0 (by positivity)]
      have := ht'.1; rw [inv_div]; linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hl := abs_lap2_le (K2 t' x y)
    have hGn := G_nonneg (d := d) (mul_pos hc ht'0) (x - y)
    have hG2n := G_nonneg (d := d) (by positivity : 0 < 2 * (c * t)) (x - y)
    have hA := KH.hA
    have hM := hhol.1
    calc |h y| * (1 / 2 * |lap2 (K2 t' x y)|)
        ≤ M0 * (1 / 2 * (d * (A * t' ^ (-(1 : ℝ)) * G d (c * t') (x - y)))) := by
          gcongr
          · exact hhol.2.2.1 y hy
          · exact hl.trans (mul_le_mul_of_nonneg_left hK2 hd)
      _ ≤ M0 * (1 / 2 * (d * (A * (2 / t) * ((4 : ℝ) ^ ((d : ℝ) / 2) * G d (2 * (c * t)) (x - y))))) := by
          gcongr
      _ = C * G d (2 * (c * t)) (x - y) := by rw [hC]; ring
  · exact (ae_restrict_iff' KH.hS).mpr (Eventually.of_forall fun y hy t' ht' =>
      (KH.heat t' (by linarith [ht'.1, half_pos ht]) x y).const_mul (h y))

end TimeDeriv

section TimeEq

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

variable [IFacts d]

end TimeEq

section KTime

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

variable [IFacts d]

/-- `lap2` as a continuous linear map. -/
noncomputable def lap2L (d : ℕ) : (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp
    (ContinuousLinearMap.apply ℝ (Eu d →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ)))

lemma lap2L_apply (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : lap2L d B = lap2 B := by
  simp [lap2L, lap2]

lemma KHyp.tm3 (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S))
    (x : Eu d) : AEStronglyMeasurable (fun t => kw3 S K3 h t x) (volume.restrict (Ioi 0)) := by
  unfold kw3
  exact AEStronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × Eu d => h p.2 • K3 p.1 x p.2)
    (hh.comp_snd.smul (KH.m3 x).aestronglyMeasurable)

lemma KHyp.int_lap2_kw2 (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s')
    {x : Eu d} (hx : x ∈ S) :
    IntervalIntegrable (fun σ => (1 / 2 : ℝ) * lap2 (kw2 S K2 h σ x)) volume s s' := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hss]
  refine (integrableOn_const (C := (1 / 2 : ℝ) * (d * (A * s ^ (-(1 : ℝ)) * M0)))
    measure_Ioc_lt_top.ne).mono' ?_ ?_
  · exact ((continuous_lap2.comp_aestronglyMeasurable
      ((KH.tm2 hh x).mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hs.le))))).const_mul _
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun σ hσ => ?_)
    have hσ0 : 0 < σ := lt_trans hs hσ.1
    have h2 := KH.kw2_le hhol hh hσ0 hx
    have hp : σ ^ (-(1 : ℝ)) ≤ s ^ (-(1 : ℝ)) := rpow_le_rpow_of_nonpos hs hσ.1.le (by norm_num)
    have hM0 : 0 ≤ M0 := hhol.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((abs_lap2_le _).trans ?_) (by norm_num)
    refine mul_le_mul_of_nonneg_left (h2.trans ?_) (Nat.cast_nonneg d)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp KH.hA) hM0

/-- Integrated heat equation for `kw0`. -/
lemma KHyp.kw0_time_diff (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s')
    {x : Eu d} (hx : x ∈ S) :
    kw0 S K h s' x - kw0 S K h s x = ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 S K2 h σ x) := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun σ => kw0 S K h σ x)
    (fun σ hσ => ?_)
    (KH.int_lap2_kw2 hhol hh hs hss hx)).symm
  rw [uIcc_of_le hss] at hσ
  exact KH.hasDerivAt_kw0_t hhol hh (lt_of_lt_of_le hs hσ.1) hx

/-- The time-difference identity for `kw1` at interior points. -/
lemma KHyp.kw1_time_diff (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x r ⊆ S) :
    kw1 S K1 h s' x - kw1 S K1 h s x =
      ∫ σ in s..s', (1 / 2 : ℝ) • (lap2L d).comp (kw3 S K3 h σ x) := by
  have hx : x ∈ S := hball (Metric.mem_ball_self hr)
  have hM0 : 0 ≤ M0 := hhol.1
  set B : ℝ := (1 / 2 : ℝ) * (‖lap2L d‖ * (A * s ^ (-(3 / 2 : ℝ)) * Hh *
    (gm d * (c * s') ^ (μ / 2)))) with hB
  have hg : HasFDerivAt (fun x' => ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 S K2 h σ x'))
      (∫ σ in s..s', (1 / 2 : ℝ) • (lap2L d).comp (kw3 S K3 h σ x)) x := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => B)
      (F := fun x' σ => (1 / 2 : ℝ) * lap2 (kw2 S K2 h σ x'))
      (F' := fun x' σ => (1 / 2 : ℝ) • (lap2L d).comp (kw3 S K3 h σ x'))
      (Metric.ball_mem_nhds x hr) ?_ (KH.int_lap2_kw2 hhol hh hs hss hx) ?_ ?_ intervalIntegrable_const ?_
    · refine Eventually.of_forall fun x' => ?_
      rw [uIoc_of_le hss]
      exact ((continuous_lap2.comp_aestronglyMeasurable
        ((KH.tm2 hh x').mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hs.le))))).const_mul _
    · rw [uIoc_of_le hss]
      have hc : Continuous fun B : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ => (lap2L d).comp B := by
        fun_prop
      exact (hc.comp_aestronglyMeasurable
        ((KH.tm3 hh x).mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hs.le)))).const_smul (1 / 2 : ℝ)
    · refine Eventually.of_forall fun σ hσ x' hx' => ?_
      rw [uIoc_of_le hss] at hσ
      have hσ0 : 0 < σ := lt_trans hs hσ.1
      have h3 := KH.kw3_hol hhol hh hμ0 hμ2 hσ0 (hball hx')
      have hp : σ ^ (-(3 / 2 : ℝ)) ≤ s ^ (-(3 / 2 : ℝ)) :=
        rpow_le_rpow_of_nonpos hs hσ.1.le (by norm_num)
      have hq : (c * σ) ^ (μ / 2) ≤ (c * s') ^ (μ / 2) :=
        rpow_le_rpow (mul_nonneg KH.hc.le hσ0.le) (mul_le_mul_of_nonneg_left hσ.2 KH.hc.le)
          (by linarith)
      have hHh : 0 ≤ Hh := hhol.2.1
      have hgm : 0 ≤ gm d := (gm_pos d).le
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), hB]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (h3.trans ?_) (norm_nonneg _))
      have e1 : A * σ ^ (-(3 / 2 : ℝ)) * Hh ≤ A * s ^ (-(3 / 2 : ℝ)) * Hh :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp KH.hA) hHh
      exact mul_le_mul e1 (mul_le_mul_of_nonneg_left hq hgm)
        (mul_nonneg hgm (rpow_nonneg (mul_nonneg KH.hc.le hσ0.le) _))
        (mul_nonneg (mul_nonneg KH.hA (rpow_nonneg hs.le _)) hHh)
    · refine Eventually.of_forall fun σ hσ x' _ => ?_
      rw [uIoc_of_le hss] at hσ
      have hσ0 : 0 < σ := lt_trans hs hσ.1
      have h2 := KH.hasFDerivAt_kw2 hh hhol.2.2.1 hσ0 x'
      have h3 := ((lap2L d).hasFDerivAt.comp x' h2).const_mul (1 / 2 : ℝ)
      have e : (fun x => (1 / 2 : ℝ) * lap2 (kw2 S K2 h σ x)) =
          fun x => (1 / 2 : ℝ) * ((lap2L d) ∘ (kw2 S K2 h σ)) x := by
        funext x; simp only [Function.comp, lap2L_apply]
      rw [e]
      exact h3
  have hf : HasFDerivAt (fun x' => kw0 S K h s' x' - kw0 S K h s x')
      (kw1 S K1 h s' x - kw1 S K1 h s x) x :=
    (KH.hasFDerivAt_kw0 hh hhol.2.2.1 (lt_of_lt_of_le hs hss) x).sub
      (KH.hasFDerivAt_kw0 hh hhol.2.2.1 hs x)
  have heq : (fun x' => kw0 S K h s' x' - kw0 S K h s x') =ᶠ[𝓝 x]
      (fun x' => ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 S K2 h σ x')) := by
    filter_upwards [Metric.ball_mem_nhds x hr] with x' hx'
    exact KH.kw0_time_diff hhol hh hs hss (hball hx')
  exact (hf.congr_of_eventuallyEq heq.symm).unique hg

/-- Time-Lipschitz bound for `kw1` on `[s, s']`. -/
lemma KHyp.kw1_time_le (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x r ⊆ S) :
    ‖kw1 S K1 h s' x - kw1 S K1 h s x‖ ≤
      (1 / 2 : ℝ) * (‖lap2L d‖ * (A * s ^ (-(3 / 2 : ℝ)) * Hh *
        (gm d * (c * s') ^ (μ / 2)))) * (s' - s) := by
  have hx : x ∈ S := hball (Metric.mem_ball_self hr)
  rw [KH.kw1_time_diff hhol hh hμ0 hμ2 hs hss hr hball]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := s')
    (f := fun σ => (1 / 2 : ℝ) • (lap2L d).comp (kw3 S K3 h σ x))
    (C := (1 / 2 : ℝ) * (‖lap2L d‖ * (A * s ^ (-(3 / 2 : ℝ)) * Hh *
        (gm d * (c * s') ^ (μ / 2))))) (fun σ hσ => ?_)
  · rwa [abs_of_nonneg (by linarith)] at this
  · rw [uIoc_of_le hss] at hσ
    have hσ0 : 0 < σ := lt_trans hs hσ.1
    have h3 := KH.kw3_hol hhol hh hμ0 hμ2 hσ0 hx
    have hp : σ ^ (-(3 / 2 : ℝ)) ≤ s ^ (-(3 / 2 : ℝ)) :=
      rpow_le_rpow_of_nonpos hs hσ.1.le (by norm_num)
    have hq : (c * σ) ^ (μ / 2) ≤ (c * s') ^ (μ / 2) :=
      rpow_le_rpow (mul_nonneg KH.hc.le hσ0.le) (mul_le_mul_of_nonneg_left hσ.2 KH.hc.le)
        (by linarith)
    have hHh : 0 ≤ Hh := hhol.2.1
    have hgm : 0 ≤ gm d := (gm_pos d).le
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (h3.trans ?_) (norm_nonneg _))
    have e1 : A * σ ^ (-(3 / 2 : ℝ)) * Hh ≤ A * s ^ (-(3 / 2 : ℝ)) * Hh :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp KH.hA) hHh
    exact mul_le_mul e1 (mul_le_mul_of_nonneg_left hq hgm)
      (mul_nonneg hgm (rpow_nonneg (mul_nonneg KH.hc.le hσ0.le) _))
      (mul_nonneg (mul_nonneg KH.hA (rpow_nonneg hs.le _)) hHh)

end KTime

end ObliqueLib

open ObliqueLib in
set_option maxHeartbeats 1000000 in
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
  let lap2 : {d : ℕ} → (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → ℝ := fun {d : ℕ} (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) => (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1));
  let lap2L : (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := (∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ))));
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S), |kw0 S K h t x - h x| ≤ A * Hh * (gm * (c * t) ^ (μ / 2))) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S), HasDerivAt (fun t => kw0 S K h t x) ((1 / 2 : ℝ) * lap2 (kw2 S K2 h t x)) t) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S), kw0 S K h s' x - kw0 S K h s x = ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 S K2 h σ x)) ∧
    (∀ {S : Set (EuclideanSpace ℝ (Fin d))} {K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} {K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {A c : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (KH : KHyp S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ S), ‖kw1 S K1 h s' x - kw1 S K1 h s x‖ ≤ (1 / 2 : ℝ) * (‖lap2L‖ * (A * s ^ (-(3 / 2 : ℝ)) * Hh * (gm * (c * s') ^ (μ / 2)))) * (s' - s)) := by
  intro d
  intro G gm KHyp HolderOnS kw0 kw1 kw2 lap2 lap2L
  obtain ⟨f_KHyp_sm0, f_KHyp_sm2, f_KHyp_hasFDerivAt_kw0, f_KHyp_hasFDerivAt_kw1, f_KHyp_hasFDerivAt_kw2, f_KHyp_kw0_le, f_KHyp_kw1_le, f_KHyp_kw2_le, f_KHyp_kw1_hol, f_KHyp_kw2_hol, f_KHyp_kw3_hol, f_KHyp_tm2, f_KHyp_kw1_lip⟩ := @EthierKurtz.kernel_potential_derivative_estimates d
  haveI : ObliqueLib.IFacts d := ⟨f_KHyp_sm0, f_KHyp_sm2, f_KHyp_hasFDerivAt_kw0, f_KHyp_hasFDerivAt_kw2, f_KHyp_kw2_le, f_KHyp_kw3_hol, f_KHyp_tm2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh hμ0 hμ2 t ht x hx; exact ObliqueLib.KHyp.kw0_sub_h KH hhol hh hμ0 hμ2 ht hx
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh t ht x hx; exact ObliqueLib.KHyp.hasDerivAt_kw0_t KH hhol hh ht hx
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh s s' hs hss x hx; exact ObliqueLib.KHyp.kw0_time_diff KH hhol hh hs hss hx
  · intro S K K1 K2 K3 A c h μ M0 Hh KH hhol hh hμ0 hμ2 s s' hs hss x r hr hball; exact ObliqueLib.KHyp.kw1_time_le KH hhol hh hμ0 hμ2 hs hss hr hball
