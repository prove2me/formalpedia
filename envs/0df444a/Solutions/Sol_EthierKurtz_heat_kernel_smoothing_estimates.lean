-- Prove2me | solution 1 for EthierKurtz.heat_kernel_smoothing_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T13:59:53.527092+00:00
-- url     : https://prove2.me/submissions/5e429739-bb3b-4ac8-981c-246457036f17

import Mathlib
import Theorems.Thm_EthierKurtz_kernel_potential_derivative_estimates
import Theorems.Thm_EthierKurtz_kernel_potential_time_estimates
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus

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

/-- Gaussian moment constant. -/
noncomputable def gm (d : ℕ) : ℝ := 1 + 2 * 2 ^ ((d : ℝ) / 2)

lemma integrable_G_sub {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Eu d) :
    Integrable (fun y : Eu d => G d s (x - y)) :=
  (integrable_G hs).comp_sub_left x

lemma integral_G_sub {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Eu d) :
    ∫ y : Eu d, G d s (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun z => G d s z) volume x, integral_G hs]

/-- Shifting the centre of a Gaussian by less than `1`. -/
lemma G_shift_le {d : ℕ} {s : ℝ} (hs : 0 < s) {x x₀ y : Eu d} (hx : ‖x - x₀‖ < 1) :
    G d s (x - y) ≤ rexp (1 / s) * 2 ^ ((d : ℝ) / 2) * G d (2 * s) (x₀ - y) := by
  unfold G
  have hn : (π * s) ^ (-((d : ℝ) / 2)) = 2 ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) := by
    rw [show π * (2 * s) = 2 * (π * s) by ring,
      mul_rpow (x := 2) (y := π * s) (by norm_num) (by positivity), ← mul_assoc,
      ← rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  have htri : ‖x₀ - y‖ ≤ 1 + ‖x - y‖ := by
    calc ‖x₀ - y‖ = ‖(x₀ - x) + (x - y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x₀ - x‖ + ‖x - y‖ := norm_add_le _ _
      _ ≤ 1 + ‖x - y‖ := by rw [norm_sub_rev]; linarith
  have he : -‖x - y‖ ^ 2 / s ≤ 1 / s + -‖x₀ - y‖ ^ 2 / (2 * s) := by
    rw [div_add_div _ _ hs.ne' (by positivity), div_le_div_iff₀ hs (by positivity)]
    have h0 : 0 ≤ ‖x₀ - y‖ := norm_nonneg _
    have hq : ‖x₀ - y‖ ^ 2 ≤ 2 + 2 * ‖x - y‖ ^ 2 := by
      linarith [sq_nonneg (‖x - y‖ - 1), mul_self_le_mul_self h0 htri]
    have := mul_le_mul_of_nonneg_left hq (le_of_lt (mul_pos hs hs))
    linarith [this]
  rw [hn]
  calc 2 ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) * rexp (-‖x - y‖ ^ 2 / s)
      ≤ 2 ^ ((d : ℝ) / 2) * (π * (2 * s)) ^ (-((d : ℝ) / 2)) *
          (rexp (1 / s) * rexp (-‖x₀ - y‖ ^ 2 / (2 * s))) := by
        rw [← Real.exp_add]; gcongr
    _ = _ := by ring

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

theorem KHyp.b0 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.1

theorem KHyp.b1 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.1

theorem KHyp.b2 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.2.1

theorem KHyp.b3 (h : KHyp d S K K1 K2 K3 A c) : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K3 t x y‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * G d (c * t) (x - y) := h.2.2.2.2.2.2.2.2.2.2.1

end KHypDef

/-- `h` is bounded by `M0` and `μ`-Hölder with constant `Hh` on `S`. -/
def HolderOnS {d : ℕ} (S : Set (Eu d)) (μ M0 Hh : ℝ) (h : Eu d → ℝ) : Prop :=
  0 ≤ M0 ∧ 0 ≤ Hh ∧ (∀ y ∈ S, |h y| ≤ M0) ∧ ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ

/-- Trace of a bilinear form in the standard basis (twice the generator `Δ/2` acts as `lap2/2`). -/
noncomputable def lap2 {d : ℕ} (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : ℝ :=
  ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

section C1Hdef

/-- `ψ` is bounded, differentiable with bounded, continuous, `μ`-Hölder derivative `ψ1`. -/
@[reducible] def C1H (d : ℕ) (μ M0 M1 H : ℝ) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) : Prop :=
  (∀ y, HasFDerivAt ψ (ψ1 y) y) ∧ Continuous ψ1 ∧ (∀ y, |ψ y| ≤ M0) ∧ (∀ y, ‖ψ1 y‖ ≤ M1) ∧
    (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H

variable {d : ℕ} {μ M0 M1 H : ℝ} {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)}

theorem C1H.hd (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, HasFDerivAt ψ (ψ1 y) y := hC.1

theorem C1H.b0 (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, |ψ y| ≤ M0 := hC.2.2.1

theorem C1H.b1 (hC : C1H d μ M0 M1 H ψ ψ1) : ∀ y, ‖ψ1 y‖ ≤ M1 := hC.2.2.2.1

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

section TimeDeriv

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

end TimeDeriv

section TimeEq

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh lam : ℝ}

end TimeEq

section KTime

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}
  {h : Eu d → ℝ} {μ M0 Hh : ℝ}

/-- `lap2` as a continuous linear map. -/
noncomputable def lap2L (d : ℕ) : (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp
    (ContinuousLinearMap.apply ℝ (Eu d →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ)))

end KTime

section GDeriv

variable {d : ℕ}

noncomputable local instance instL2N' (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S' (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The real inner product as a continuous bilinear map. -/
noncomputable def Ip (d : ℕ) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ := innerSL ℝ

noncomputable def ge (d : ℕ) (a : ℝ) (z : Eu d) : ℝ := rexp (-(a * ‖z‖ ^ 2))

noncomputable def gK1 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] ℝ := (-(2 * a) * ge d a z) • Ip d z

noncomputable def gK2 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ge d a z • ((4 * a ^ 2) • (Ip d z).smulRight (Ip d z) - (2 * a) • Ip d)

noncomputable def gK3 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  fderiv ℝ (gK2 a) z

end GDeriv

section Whole

variable {d : ℕ}

noncomputable local instance instL2N5 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S5 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Normalisation of the heat kernel at time `t`. -/
noncomputable def hN (d : ℕ) (t : ℝ) : ℝ := (π * (2 * t)) ^ (-((d : ℝ) / 2))

noncomputable def wK (d : ℕ) (t : ℝ) (x y : Eu d) : ℝ := G d (2 * t) (x - y)

noncomputable def wK1 (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] ℝ := hN d t • gK1 (1 / (2 * t)) (x - y)

noncomputable def wK2 (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • gK2 (1 / (2 * t)) (x - y)

noncomputable def wK3 (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • gK3 (1 / (2 * t)) (x - y)

/-- The constant of the whole-space kernel bounds. -/
noncomputable def wA (d : ℕ) : ℝ := 51 * 2 ^ ((d : ℝ) / 2)

end Whole

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  KHyp_hasFDerivAt_kw0 : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw0 S K h t) (kw1 S K1 h t x) x
  KHyp_hasFDerivAt_kw1 : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw1 S K1 h t) (kw2 S K2 h t x) x
  KHyp_hasFDerivAt_kw2 : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw2 S K2 h t) (kw3 S K3 h t x) x
  KHyp_kw0_le : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), |kw0 S K h t x| ≤ A * M0
  KHyp_kw1_le : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * M0
  KHyp_kw1_hol : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2))
  KHyp_kw2_hol : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2))
  KHyp_kw1_lip : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x x' : Eu d} (hx : x ∈ S) (hx' : x' ∈ S), ‖kw1 S K1 h t x - kw1 S K1 h t x'‖ ≤ A * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖
  KHyp_kw0_sub_h : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), |kw0 S K h t x - h x| ≤ A * Hh * (gm d * (c * t) ^ (μ / 2))
  KHyp_hasDerivAt_kw0_t : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), HasDerivAt (fun t => kw0 S K h t x) ((1 / 2 : ℝ) * lap2 (kw2 S K2 h t x)) t
  KHyp_kw0_time_diff : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} (hx : x ∈ S), kw0 S K h s' x - kw0 S K h s x = ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 S K2 h σ x)
  KHyp_kw1_time_le : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ S), ‖kw1 S K1 h s' x - kw1 S K1 h s x‖ ≤ (1 / 2 : ℝ) * (‖lap2L d‖ * (A * s ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (c * s') ^ (μ / 2)))) * (s' - s)
  gK2_apply : ∀ (a : ℝ) (z v w : Eu d), gK2 a z v w = ge d a z * (4 * a ^ 2 * inner ℝ z v * inner ℝ z w - 2 * a * inner ℝ v w)
  G_eq_ge : ∀ (s : ℝ) (z : Eu d), G d s z = (π * s) ^ (-((d : ℝ) / 2)) * ge d (1 / s) z
  wK_d1 : ∀ (t : ℝ) (x y : Eu d), HasFDerivAt (fun x => wK d t x y) (wK1 t x y) x
  wK_d2 : ∀ (t : ℝ) (x y : Eu d), HasFDerivAt (fun x => wK1 t x y) (wK2 t x y) x
  wK_d3 : ∀ (t : ℝ) (x y : Eu d), HasFDerivAt (fun x => wK2 t x y) (wK3 t x y) x
  hN_ge : ∀ {t : ℝ} (ht : 0 < t) (z : Eu d), hN d t * ge d (1 / (2 * t)) z = G d (2 * t) z
  wA_nonneg : 0 ≤ wA d
  whole_bounds : ∀ {t : ℝ} (ht : 0 < t) (x y : Eu d), |wK d t x y| ≤ wA d * G d (4 * t) (x - y) ∧ ‖wK1 t x y‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK2 t x y‖ ≤ wA d * t ^ (-(1 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK3 t x y‖ ≤ wA d * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) (x - y)

end IFk

export IFacts (gK2_apply G_eq_ge wK_d1 wK_d2 wK_d3 hN_ge wA_nonneg whole_bounds)

theorem KHyp.hasFDerivAt_kw0 {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw0 S K h t) (kw1 S K1 h t x) x := IFacts.KHyp_hasFDerivAt_kw0

theorem KHyp.hasFDerivAt_kw1 {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw1 S K1 h t) (kw2 S K2 h t x) x := IFacts.KHyp_hasFDerivAt_kw1

theorem KHyp.hasFDerivAt_kw2 {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {M0 : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hh : AEStronglyMeasurable h (volume.restrict S)) (hhb : ∀ y ∈ S, |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d), HasFDerivAt (kw2 S K2 h t) (kw3 S K3 h t x) x := IFacts.KHyp_hasFDerivAt_kw2

theorem KHyp.kw0_le {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), |kw0 S K h t x| ≤ A * M0 := IFacts.KHyp_kw0_le

theorem KHyp.kw1_le {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * M0 := IFacts.KHyp_kw1_le

theorem KHyp.kw1_hol {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw1 S K1 h t x‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) := IFacts.KHyp_kw1_hol

theorem KHyp.kw2_hol {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), ‖kw2 S K2 h t x‖ ≤ A * t ^ (-(1 : ℝ)) * Hh * (gm d * (c * t) ^ (μ / 2)) := IFacts.KHyp_kw2_hol

theorem KHyp.kw1_lip {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x x' : Eu d} (hx : x ∈ S) (hx' : x' ∈ S), ‖kw1 S K1 h t x - kw1 S K1 h t x'‖ ≤ A * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖ := IFacts.KHyp_kw1_lip

theorem KHyp.kw0_sub_h {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), |kw0 S K h t x - h x| ≤ A * Hh * (gm d * (c * t) ^ (μ / 2)) := IFacts.KHyp_kw0_sub_h

theorem KHyp.hasDerivAt_kw0_t {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ S), HasDerivAt (fun t => kw0 S K h t x) ((1 / 2 : ℝ) * lap2 (kw2 S K2 h t x)) t := IFacts.KHyp_hasDerivAt_kw0_t

theorem KHyp.kw0_time_diff {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} (hx : x ∈ S), kw0 S K h s' x - kw0 S K h s x = ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 S K2 h σ x) := IFacts.KHyp_kw0_time_diff

theorem KHyp.kw1_time_le {d : ℕ} [IFacts d] : ∀ {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ} {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)} {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ} {h : Eu d → ℝ} {μ M0 Hh : ℝ} (KH : KHyp d S K K1 K2 K3 A c) (hhol : HolderOnS S μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict S)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ S), ‖kw1 S K1 h s' x - kw1 S K1 h s x‖ ≤ (1 / 2 : ℝ) * (‖lap2L d‖ * (A * s ^ (-(3 / 2 : ℝ)) * Hh * (gm d * (c * s') ^ (μ / 2)))) * (s' - s) := IFacts.KHyp_kw1_time_le

section Whole2

variable {d : ℕ}

variable [IFacts d]

noncomputable local instance instL2N6 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S6 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

lemma contDiff_ge_uncurry : ContDiff ℝ ⊤ (fun p : ℝ × Eu d => ge d p.1 p.2) := by
  unfold ge
  exact (contDiff_fst.mul ((contDiff_norm_sq ℝ).comp contDiff_snd)).neg.exp

lemma contDiff_gK2_uncurry : ContDiff ℝ ⊤ (fun p : ℝ × Eu d => gK2 p.1 p.2) := by
  have hI : ContDiff ℝ ⊤ (fun p : ℝ × Eu d => Ip d p.2) := (Ip d).contDiff.comp contDiff_snd
  have hB := hI.smulRight hI
  have hM : ContDiff ℝ ⊤ (fun p : ℝ × Eu d =>
      (4 * p.1 ^ 2) • (Ip d p.2).smulRight (Ip d p.2) - (2 * p.1) • Ip d) :=
    ((contDiff_const.mul (contDiff_fst.pow 2)).smul hB).sub
      ((contDiff_const.mul contDiff_fst).smul contDiff_const)
  exact contDiff_ge_uncurry.smul hM

lemma continuous_gK1_uncurry : Continuous (fun p : ℝ × Eu d => gK1 p.1 p.2) :=
  ((continuous_const.mul continuous_fst).neg.mul contDiff_ge_uncurry.continuous).smul
    ((Ip d).continuous.comp continuous_snd)

lemma continuous_gK3_uncurry : Continuous (fun p : ℝ × Eu d => gK3 p.1 p.2) := by
  have h := ContDiff.fderiv (𝕜 := ℝ) (m := ⊤) (n := 0)
    (f := fun (q : ℝ × Eu d) (z : Eu d) => gK2 q.1 z) (g := fun q => q.2)
    (contDiff_gK2_uncurry.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd le_top
  exact h.continuous

lemma sm_T (x : Eu d) : StronglyMeasurable (fun p : ℝ × Eu d => ((1 / (2 * p.1) : ℝ), x - p.2)) :=
  ((measurable_const.div (measurable_const.mul measurable_fst)).prodMk
    (measurable_const.sub measurable_snd)).stronglyMeasurable

lemma sm_hN : StronglyMeasurable (fun p : ℝ × Eu d => hN d p.1) := by
  unfold hN
  exact ((measurable_const.mul (measurable_const.mul measurable_fst)).pow_const _).stronglyMeasurable

lemma wK_eq (t : ℝ) (x y : Eu d) : wK d t x y = hN d t * ge d (1 / (2 * t)) (x - y) := by
  rw [wK, G_eq_ge, hN]

lemma wK2_trace {t : ℝ} (ht : 0 < t) (x y : Eu d) :
    lap2 (wK2 t x y) = G d (2 * t) (x - y) * (‖x - y‖ ^ 2 / t ^ 2 - d / t) := by
  unfold lap2
  have hs : ∀ i, inner ℝ (x - y) (EuclideanSpace.single i (1 : ℝ)) = (x - y) i := by
    intro i; simp [EuclideanSpace.inner_single_right]
  have h1 : ∀ i : Fin d, inner ℝ (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) = 1 := by
    intro i; simp [EuclideanSpace.inner_single_right]
  simp only [wK2, ContinuousLinearMap.smul_apply, smul_eq_mul, gK2_apply, hs, h1]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_assoc, hN_ge ht]
  congr 1
  rw [Finset.sum_sub_distrib, EuclideanSpace.real_norm_sq_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : ∀ i, 4 * (1 / (2 * t)) ^ 2 * (x - y) i * (x - y) i = 1 / t ^ 2 * (x - y) i ^ 2 := by
    intro i; field_simp; ring
  simp only [this]
  rw [← Finset.mul_sum]
  field_simp

lemma wK_heat {t : ℝ} (ht : 0 < t) (x y : Eu d) :
    HasDerivAt (fun t => wK d t x y) ((1 / 2 : ℝ) * lap2 (wK2 t x y)) t := by
  set z := x - y
  have hpos : 0 < π * (2 * t) := by positivity
  have hA : HasDerivAt (fun t : ℝ => π * (2 * t)) (π * (2 * 1)) t :=
    ((hasDerivAt_id t).const_mul 2).const_mul π
  have hP := hA.rpow_const (p := -((d : ℝ) / 2)) (Or.inl hpos.ne')
  have hQ : HasDerivAt (fun t : ℝ => -‖z‖ ^ 2 / (2 * t))
      ((0 * (2 * t) - -‖z‖ ^ 2 * (2 * 1)) / (2 * t) ^ 2) t :=
    (hasDerivAt_const t (-‖z‖ ^ 2)).div ((hasDerivAt_id t).const_mul 2) (by positivity)
  have hE := hQ.exp
  have hPE := hP.mul hE
  refine hPE.congr_deriv ?_
  rw [wK2_trace ht, G, rpow_sub_one hpos.ne']
  field_simp
  ring

lemma wK_mass {t : ℝ} (ht : 0 < t) (x : Eu d) : ∫ y in univ, wK d t x y = 1 := by
  rw [Measure.restrict_univ]; exact integral_G_sub (by positivity) x

/-- The whole-space heat kernel satisfies the kernel hypotheses on `S = univ`. -/
theorem wholeKHyp (d : ℕ) [IFacts d] : KHyp d univ (wK d) wK1 wK2 wK3 (wA d) 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact wA_nonneg
  · exact by norm_num
  · exact MeasurableSet.univ
  · exact convex_univ
  · exact fun t _ x y => wK_d1 t x y
  · exact fun t _ x y => wK_d2 t x y
  · exact fun t _ x y => wK_d3 t x y
  · exact fun t ht x _ y _ => (whole_bounds ht x y).1
  · exact fun t ht x _ y _ => (whole_bounds ht x y).2.1
  · exact fun t ht x _ y _ => (whole_bounds ht x y).2.2.1
  · exact fun t ht x _ y _ => (whole_bounds ht x y).2.2.2
  · exact fun x => by
      rw [show (fun p : ℝ × Eu d => wK d p.1 x p.2) = fun p => hN d p.1 * ge d (1 / (2 * p.1)) (x - p.2)
        from funext fun p => wK_eq p.1 x p.2]
      exact sm_hN.mul ((contDiff_ge_uncurry (d := d)).continuous.comp_stronglyMeasurable (sm_T x))
  · exact fun x => sm_hN.smul (continuous_gK1_uncurry.comp_stronglyMeasurable (sm_T x))
  · exact fun x => sm_hN.smul (contDiff_gK2_uncurry.continuous.comp_stronglyMeasurable (sm_T x))
  · exact fun x => sm_hN.smul (continuous_gK3_uncurry.comp_stronglyMeasurable (sm_T x))
  · exact fun t ht x₀ => by
      set C := wA d * (1 + t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 : ℝ)) + t ^ (-(3 / 2 : ℝ))) *
        (rexp (1 / (4 * t)) * 2 ^ ((d : ℝ) / 2))
      refine ⟨1, one_pos, fun y => C * G d (2 * (4 * t)) (x₀ - y),
        ((integrable_G_sub (by positivity) x₀).const_mul C).integrableOn, fun x hx y _ => ?_⟩
      have hx' : ‖x - x₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
      have hsh := G_shift_le (d := d) (by positivity : 0 < 4 * t) (y := y) hx'
      obtain ⟨b0, b1, b2, b3⟩ := whole_bounds (d := d) ht x y
      have hW := wA_nonneg (d := d)
      have p1 := rpow_nonneg ht.le (-(1 / 2 : ℝ))
      have p2 := rpow_nonneg ht.le (-(1 : ℝ))
      have p3 := rpow_nonneg ht.le (-(3 / 2 : ℝ))
      have hG4 := G_nonneg (d := d) (by positivity : 0 < 4 * t) (x - y)
      have key : ∀ q : ℝ, 0 ≤ q → q ≤ 1 + t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 : ℝ)) + t ^ (-(3 / 2 : ℝ)) →
          wA d * q * G d (4 * t) (x - y) ≤ C * G d (2 * (4 * t)) (x₀ - y) := fun q hq hqle => by
        calc wA d * q * G d (4 * t) (x - y)
            ≤ wA d * (1 + t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 : ℝ)) + t ^ (-(3 / 2 : ℝ))) *
                (rexp (1 / (4 * t)) * 2 ^ ((d : ℝ) / 2) * G d (2 * (4 * t)) (x₀ - y)) := by
              gcongr
          _ = C * G d (2 * (4 * t)) (x₀ - y) := by ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact b0.trans ((le_of_eq (by ring)).trans (key 1 zero_le_one (by linarith)))
      · exact b1.trans (key _ p1 (by linarith))
      · exact b2.trans (key _ p2 (by linarith))
      · exact b3.trans (key _ p3 (by linarith))
  · exact fun t ht x y => wK_heat ht x y
  · exact fun t ht x => wK_mass ht x

end Whole2

section Transfer

variable {d : ℕ} {ψ : Eu d → ℝ} {ψ1 : Eu d → (Eu d →L[ℝ] ℝ)} {M0 M1 : ℝ}

variable [IFacts d]

lemma kw0_whole_eq (h : Eu d → ℝ) (t : ℝ) (x : Eu d) :
    kw0 univ (wK d) h t x = ∫ z, h (x - z) * G d (2 * t) z := by
  unfold kw0 wK
  rw [Measure.restrict_univ]
  rw [← integral_sub_left_eq_self (fun z => h (x - z) * G d (2 * t) z) volume x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel, smul_eq_mul]

lemma hasFDerivAt_kw0_trans (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1)
    (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    HasFDerivAt (kw0 univ (wK d) ψ t) (∫ z, G d (2 * t) z • ψ1 (x - z)) x := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  have ht2 : 0 < 2 * t := by positivity
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans (hb1 0)
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hb0 0)
  have e : kw0 univ (wK d) ψ t = fun x' => ∫ z, ψ (x' - z) * G d (2 * t) z := by
    funext x'; exact kw0_whole_eq ψ t x'
  rw [e]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x' z => ψ (x' - z) * G d (2 * t) z)
    (F' := fun x' z => G d (2 * t) z • ψ1 (x' - z)) (bound := fun z => M1 * G d (2 * t) z)
    (Metric.ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ((integrable_G ht2).const_mul M1) ?_
  · exact Eventually.of_forall fun x' =>
      ((hψc.comp (continuous_const.sub continuous_id)).mul (continuous_G _)).aestronglyMeasurable
  · refine ((integrable_G ht2).const_mul M0).mono'
      ((hψc.comp (continuous_const.sub continuous_id)).mul (continuous_G _)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (G_nonneg ht2 z)]
    exact mul_le_mul_of_nonneg_right (hb0 _) (G_nonneg ht2 z)
  · exact ((continuous_G _).smul (hc1.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine Eventually.of_forall fun z x' _ => ?_
    rw [norm_smul, Real.norm_of_nonneg (G_nonneg ht2 z), mul_comm]
    exact mul_le_mul_of_nonneg_right (hb1 _) (G_nonneg ht2 z)
  · refine Eventually.of_forall fun z x' _ => ?_
    have h1 : HasFDerivAt (fun x' : Eu d => x' - z) (ContinuousLinearMap.id ℝ (Eu d)) x' :=
      (hasFDerivAt_id x').sub_const z
    have h2 := ((hd (x' - z)).comp x' h1).mul_const (G d (2 * t) z)
    simpa using h2

lemma kw1_trans (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1)
    (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x v : Eu d) :
    kw1 univ wK1 ψ t x v = kw0 univ (wK d) (fun y => ψ1 y v) t x := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  have ht2 : 0 < 2 * t := by positivity
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans (hb1 0)
  have h1 := (wholeKHyp d).hasFDerivAt_kw0 (h := ψ) (M0 := M0) hψc.aestronglyMeasurable
    (fun y _ => hb0 y) ht x
  have h2 := hasFDerivAt_kw0_trans hd hc1 hb0 hb1 ht x
  rw [h1.unique h2, kw0_whole_eq]
  have hint : Integrable (fun z => G d (2 * t) z • ψ1 (x - z)) := by
    refine ((integrable_G ht2).const_mul M1).mono'
      ((continuous_G _).smul (hc1.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [norm_smul, Real.norm_of_nonneg (G_nonneg ht2 z), mul_comm]
    exact mul_le_mul_of_nonneg_right (hb1 _) (G_nonneg ht2 z)
  rw [ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma kw2_trans (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1)
    (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x u v : Eu d) :
    kw2 univ wK2 ψ t x u v = kw1 univ wK1 (fun y => ψ1 y v) t x u := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  have hv : ∀ y, |ψ1 y v| ≤ M1 * ‖v‖ := fun y => by
    rw [← Real.norm_eq_abs]
    exact ((ψ1 y).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hb1 y) (norm_nonneg v))
  have hvc : Continuous fun y => ψ1 y v := (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hc1
  have hk1 := (wholeKHyp d).hasFDerivAt_kw1 (h := ψ) (M0 := M0) hψc.aestronglyMeasurable
    (fun y _ => hb0 y) ht x
  have hL := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hk1
  have hR := (wholeKHyp d).hasFDerivAt_kw0 (h := fun y => ψ1 y v) (M0 := M1 * ‖v‖)
    hvc.aestronglyMeasurable (fun y _ => hv y) ht x
  have e : (⇑(ContinuousLinearMap.apply ℝ ℝ v) ∘ kw1 univ wK1 ψ t) =
      kw0 univ (wK d) (fun y => ψ1 y v) t := by
    funext x'
    simp only [Function.comp, ContinuousLinearMap.apply_apply]
    exact kw1_trans hd hc1 hb0 hb1 ht x' v
  rw [e] at hL
  have := congrArg (fun L : Eu d →L[ℝ] ℝ => L u) (hL.unique hR)
  simpa using this

lemma kw3_trans (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1)
    (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x w u v : Eu d) :
    kw3 univ wK3 ψ t x w u v = kw2 univ wK2 (fun y => ψ1 y v) t x w u := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  have hv : ∀ y, |ψ1 y v| ≤ M1 * ‖v‖ := fun y => by
    rw [← Real.norm_eq_abs]
    exact ((ψ1 y).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hb1 y) (norm_nonneg v))
  have hvc : Continuous fun y => ψ1 y v := (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hc1
  have hk2 := (wholeKHyp d).hasFDerivAt_kw2 (h := ψ) (M0 := M0) hψc.aestronglyMeasurable
    (fun y _ => hb0 y) ht x
  set L : (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp (ContinuousLinearMap.apply ℝ (Eu d →L[ℝ] ℝ) u)
  have hL := L.hasFDerivAt.comp x hk2
  have hR := ((ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt).comp x
    ((wholeKHyp d).hasFDerivAt_kw1 (h := fun y => ψ1 y v) (M0 := M1 * ‖v‖)
      hvc.aestronglyMeasurable (fun y _ => hv y) ht x)
  have e : (⇑L ∘ kw2 univ wK2 ψ t) =
      (⇑(ContinuousLinearMap.apply ℝ ℝ u) ∘ kw1 univ wK1 (fun y => ψ1 y v) t) := by
    funext x'
    simp only [Function.comp, L, ContinuousLinearMap.coe_comp', ContinuousLinearMap.apply_apply]
    exact kw2_trans hd hc1 hb0 hb1 ht x' u v
  rw [e] at hL
  have := congrArg (fun M : Eu d →L[ℝ] ℝ => M w) (hL.unique hR)
  simpa [L] using this

end Transfer

section WholeAPI

variable {d : ℕ} {h : Eu d → ℝ} {μ M0 Hh : ℝ}

variable [IFacts d]

noncomputable local instance instL2NW (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2SW (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

lemma wh_hasDerivAt_kw0_t (hhol : HolderOnS univ μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ (univ : Set (Eu d))) :
    HasDerivAt (fun t => kw0 univ (wK d) h t x) ((1 / 2 : ℝ) * lap2 (kw2 univ wK2 h t x)) t :=
  (wholeKHyp d).hasDerivAt_kw0_t hhol hh ht hx

lemma wh_hasFDerivAt_kw0 (hh : AEStronglyMeasurable h (volume.restrict univ))
    (hhb : ∀ y ∈ (univ : Set (Eu d)), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    HasFDerivAt (kw0 univ (wK d) h t) (kw1 univ wK1 h t x) x :=
  (wholeKHyp d).hasFDerivAt_kw0 hh hhb ht x

lemma wh_hasFDerivAt_kw1 (hh : AEStronglyMeasurable h (volume.restrict univ))
    (hhb : ∀ y ∈ (univ : Set (Eu d)), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    HasFDerivAt (kw1 univ wK1 h t) (kw2 univ wK2 h t x) x :=
  (wholeKHyp d).hasFDerivAt_kw1 hh hhb ht x

lemma wh_hasFDerivAt_kw2 (hh : AEStronglyMeasurable h (volume.restrict univ))
    (hhb : ∀ y ∈ (univ : Set (Eu d)), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    HasFDerivAt (kw2 univ wK2 h t) (kw3 univ wK3 h t x) x :=
  (wholeKHyp d).hasFDerivAt_kw2 hh hhb ht x

lemma wh_kw0_le (hhol : HolderOnS univ μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ (univ : Set (Eu d))) : |kw0 univ (wK d) h t x| ≤ wA d * M0 :=
  (wholeKHyp d).kw0_le hhol hh ht hx

lemma wh_kw0_sub_h (hhol : HolderOnS univ μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))) :
    |kw0 univ (wK d) h t x - h x| ≤ wA d * Hh * (gm d * (4 * t) ^ (μ / 2)) :=
  (wholeKHyp d).kw0_sub_h hhol hh hμ0 hμ2 ht hx

lemma wh_kw0_time_diff (hhol : HolderOnS univ μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s')
    {x : Eu d} (hx : x ∈ (univ : Set (Eu d))) :
    kw0 univ (wK d) h s' x - kw0 univ (wK d) h s x = ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 univ wK2 h σ x) :=
  (wholeKHyp d).kw0_time_diff hhol hh hs hss hx

lemma wh_kw1_hol (hhol : HolderOnS univ μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))) :
    ‖kw1 univ wK1 h t x‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * Hh * (gm d * (4 * t) ^ (μ / 2)) :=
  (wholeKHyp d).kw1_hol hhol hh hμ0 hμ2 ht hx

lemma wh_kw1_le (hhol : HolderOnS univ μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : Eu d}
    (hx : x ∈ (univ : Set (Eu d))) : ‖kw1 univ wK1 h t x‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * M0 :=
  (wholeKHyp d).kw1_le hhol hh ht hx

lemma wh_kw1_time_le (hhol : HolderOnS univ μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : Eu d} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x r ⊆ (univ : Set (Eu d))) :
    ‖kw1 univ wK1 h s' x - kw1 univ wK1 h s x‖ ≤
      (1 / 2 : ℝ) * (‖lap2L d‖ * (wA d * s ^ (-(3 / 2 : ℝ)) * Hh *
        (gm d * (4 * s') ^ (μ / 2)))) * (s' - s) :=
  (wholeKHyp d).kw1_time_le hhol hh hμ0 hμ2 hs hss hr hball

lemma wh_kw2_hol (hhol : HolderOnS univ μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    {t : ℝ} (ht : 0 < t) {x : Eu d} (hx : x ∈ (univ : Set (Eu d))) :
    ‖kw2 univ wK2 h t x‖ ≤ wA d * t ^ (-(1 : ℝ)) * Hh * (gm d * (4 * t) ^ (μ / 2)) :=
  (wholeKHyp d).kw2_hol hhol hh hμ0 hμ2 ht hx

lemma wh_kw1_lip (hhol : HolderOnS univ μ M0 Hh h)
    (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x x' : Eu d}
    (hx : x ∈ (univ : Set (Eu d))) (hx' : x' ∈ (univ : Set (Eu d))) :
    ‖kw1 univ wK1 h t x - kw1 univ wK1 h t x'‖ ≤ wA d * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖ :=
  (wholeKHyp d).kw1_lip hhol hh ht hx hx'

end WholeAPI

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
  let HolderOnS : {d : ℕ} → (S : Set (EuclideanSpace ℝ (Fin d))) → (μ M0 Hh : ℝ) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → Prop := fun {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (μ M0 Hh : ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) => (0 ≤ M0 ∧ 0 ≤ Hh ∧ (∀ y ∈ S, |h y| ≤ M0) ∧ ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ);
  let kw0 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K t x y);
  let kw1 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K1 t x y);
  let kw2 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K2 t x y);
  let kw3 : (S : Set (EuclideanSpace ℝ (Fin d))) → (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) → (h : EuclideanSpace ℝ (Fin d) → ℝ) → (t : ℝ) → (x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (S : Set (EuclideanSpace ℝ (Fin d))) (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) => (∫ y in S, h y • K3 t x y);
  let lap2 : {d : ℕ} → (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → ℝ := fun {d : ℕ} (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) => (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1));
  let lap2L : (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := (∑ i : Fin d, (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ))));
  let Ip : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := (innerSL ℝ);
  let ge : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (rexp (-(a * ‖z‖ ^ 2)));
  let gK1 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => ((-(2 * a) * ge a z) • Ip z);
  let gK2 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (ge a z • ((4 * a ^ 2) • (Ip z).smulRight (Ip z) - (2 * a) • Ip));
  let gK3 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK2 a) z);
  let hN : (t : ℝ) → ℝ := fun (t : ℝ) => ((π * (2 * t)) ^ (-((d : ℝ) / 2)));
  let wK : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (G (2 * t) (x - y));
  let wK1 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK1 (1 / (2 * t)) (x - y));
  let wK2 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK2 (1 / (2 * t)) (x - y));
  let wK3 : (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (hN t • gK3 (1 / (2 * t)) (x - y));
  let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x v : EuclideanSpace ℝ (Fin d)), kw1 univ wK1 ψ t x v = kw0 univ (wK) (fun y => ψ1 y v) t x) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x u v : EuclideanSpace ℝ (Fin d)), kw2 univ wK2 ψ t x u v = kw1 univ wK1 (fun y => ψ1 y v) t x u) ∧
    (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)} {M0 M1 : ℝ} (hd : ∀ y, HasFDerivAt ψ (ψ1 y) y) (hc1 : Continuous ψ1) (hb0 : ∀ y, |ψ y| ≤ M0) (hb1 : ∀ y, ‖ψ1 y‖ ≤ M1) {t : ℝ} (ht : 0 < t) (x w u v : EuclideanSpace ℝ (Fin d)), kw3 univ wK3 ψ t x w u v = kw2 univ wK2 (fun y => ψ1 y v) t x w u) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), HasDerivAt (fun t => kw0 univ (wK) h t x) ((1 / 2 : ℝ) * lap2 (kw2 univ wK2 h t x)) t) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin d))), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), HasFDerivAt (kw0 univ (wK) h t) (kw1 univ wK1 h t x) x) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin d))), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), HasFDerivAt (kw1 univ wK1 h t) (kw2 univ wK2 h t x) x) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {M0 : ℝ} (hh : AEStronglyMeasurable h (volume.restrict univ)) (hhb : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin d))), |h y| ≤ M0) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), HasFDerivAt (kw2 univ wK2 h t) (kw3 univ wK3 h t x) x) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), |kw0 univ (wK) h t x| ≤ wA * M0) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), |kw0 univ (wK) h t x - h x| ≤ wA * Hh * (gm * (4 * t) ^ (μ / 2))) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), kw0 univ (wK) h s' x - kw0 univ (wK) h s x = ∫ σ in s..s', (1 / 2 : ℝ) * lap2 (kw2 univ wK2 h σ x)) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw1 univ wK1 h t x‖ ≤ wA * t ^ (-(1 / 2 : ℝ)) * Hh * (gm * (4 * t) ^ (μ / 2))) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw1 univ wK1 h t x‖ ≤ wA * t ^ (-(1 / 2 : ℝ)) * M0) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw1 univ wK1 h s' x - kw1 univ wK1 h s x‖ ≤ (1 / 2 : ℝ) * (‖lap2L‖ * (wA * s ^ (-(3 / 2 : ℝ)) * Hh * (gm * (4 * s') ^ (μ / 2)))) * (s' - s)) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw2 univ wK2 h t x‖ ≤ wA * t ^ (-(1 : ℝ)) * Hh * (gm * (4 * t) ^ (μ / 2))) ∧
    (∀ {h : EuclideanSpace ℝ (Fin d) → ℝ} {μ M0 Hh : ℝ} (hhol : HolderOnS univ μ M0 Hh h) (hh : AEStronglyMeasurable h (volume.restrict univ)) {t : ℝ} (ht : 0 < t) {x x' : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))) (hx' : x' ∈ (univ : Set (EuclideanSpace ℝ (Fin d)))), ‖kw1 univ wK1 h t x - kw1 univ wK1 h t x'‖ ≤ wA * t ^ (-(1 : ℝ)) * M0 * ‖x - x'‖) := by
  intro d
  intro G gm HolderOnS kw0 kw1 kw2 kw3 lap2 lap2L Ip ge gK1 gK2 gK3 hN wK wK1 wK2 wK3 wA
  obtain ⟨f_KHyp_sm0, f_KHyp_sm2, f_KHyp_hasFDerivAt_kw0, f_KHyp_hasFDerivAt_kw1, f_KHyp_hasFDerivAt_kw2, f_KHyp_kw0_le, f_KHyp_kw1_le, f_KHyp_kw2_le, f_KHyp_kw1_hol, f_KHyp_kw2_hol, f_KHyp_kw3_hol, f_KHyp_tm2, f_KHyp_kw1_lip⟩ := @EthierKurtz.kernel_potential_derivative_estimates d
  obtain ⟨f_KHyp_kw0_sub_h, f_KHyp_hasDerivAt_kw0_t, f_KHyp_kw0_time_diff, f_KHyp_kw1_time_le⟩ := @EthierKurtz.kernel_potential_time_estimates d
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  haveI : ObliqueLib.IFacts d := ⟨f_KHyp_hasFDerivAt_kw0, f_KHyp_hasFDerivAt_kw1, f_KHyp_hasFDerivAt_kw2, f_KHyp_kw0_le, f_KHyp_kw1_le, f_KHyp_kw1_hol, f_KHyp_kw2_hol, f_KHyp_kw1_lip, f_KHyp_kw0_sub_h, f_KHyp_hasDerivAt_kw0_t, f_KHyp_kw0_time_diff, f_KHyp_kw1_time_le, f_gK2_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_ge, f_wA_nonneg, f_whole_bounds⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ψ ψ1 M0 M1 hd hc1 hb0 hb1 t ht x v; exact ObliqueLib.kw1_trans hd hc1 hb0 hb1 ht x v
  · intro ψ ψ1 M0 M1 hd hc1 hb0 hb1 t ht x u v; exact ObliqueLib.kw2_trans hd hc1 hb0 hb1 ht x u v
  · intro ψ ψ1 M0 M1 hd hc1 hb0 hb1 t ht x w u v; exact ObliqueLib.kw3_trans hd hc1 hb0 hb1 ht x w u v
  · intro h μ M0 Hh hhol hh t ht x hx; exact ObliqueLib.wh_hasDerivAt_kw0_t hhol hh ht hx
  · intro h M0 hh hhb t ht x; exact ObliqueLib.wh_hasFDerivAt_kw0 hh hhb ht x
  · intro h M0 hh hhb t ht x; exact ObliqueLib.wh_hasFDerivAt_kw1 hh hhb ht x
  · intro h M0 hh hhb t ht x; exact ObliqueLib.wh_hasFDerivAt_kw2 hh hhb ht x
  · intro h μ M0 Hh hhol hh t ht x hx; exact ObliqueLib.wh_kw0_le hhol hh ht hx
  · intro h μ M0 Hh hhol hh hμ0 hμ2 t ht x hx; exact ObliqueLib.wh_kw0_sub_h hhol hh hμ0 hμ2 ht hx
  · intro h μ M0 Hh hhol hh s s' hs hss x hx; exact ObliqueLib.wh_kw0_time_diff hhol hh hs hss hx
  · intro h μ M0 Hh hhol hh hμ0 hμ2 t ht x hx; exact ObliqueLib.wh_kw1_hol hhol hh hμ0 hμ2 ht hx
  · intro h μ M0 Hh hhol hh t ht x hx; exact ObliqueLib.wh_kw1_le hhol hh ht hx
  · intro h μ M0 Hh hhol hh hμ0 hμ2 s s' hs hss x r hr hball; exact ObliqueLib.wh_kw1_time_le hhol hh hμ0 hμ2 hs hss hr hball
  · intro h μ M0 Hh hhol hh hμ0 hμ2 t ht x hx; exact ObliqueLib.wh_kw2_hol hhol hh hμ0 hμ2 ht hx
  · intro h μ M0 Hh hhol hh t ht x x' hx hx'; exact ObliqueLib.wh_kw1_lip hhol hh ht hx hx'
