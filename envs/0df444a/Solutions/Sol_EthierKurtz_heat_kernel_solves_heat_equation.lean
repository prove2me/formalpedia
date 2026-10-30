-- Prove2me | solution 1 for EthierKurtz.heat_kernel_solves_heat_equation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T12:55:51.529152+00:00
-- url     : https://prove2.me/submissions/deea1307-f37a-4d7a-a06a-07ba5d5bbafd

import Mathlib
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
      nlinarith [sq_nonneg (‖x - y‖ - 1), mul_self_le_mul_self h0 htri]
    have := mul_le_mul_of_nonneg_left hq (le_of_lt (mul_pos hs hs))
    nlinarith [this]
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

noncomputable local instance instL1N (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL1S (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance instL1C (d : ℕ) : CompleteSpace (Eu d →L[ℝ] ℝ) := inferInstance

local instance instL2C (d : ℕ) : CompleteSpace (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance

local instance instEC (d : ℕ) : CompleteSpace (Eu d) := inferInstance

noncomputable local instance instL3N (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance instL3C (d : ℕ) : CompleteSpace (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance

local instance instL1M (d : ℕ) : ContinuousSMul ℝ (Eu d →L[ℝ] ℝ) := inferInstance

local instance instL2M (d : ℕ) : ContinuousSMul ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) := inferInstance

local instance instENI (d : ℕ) : (volume : Measure (Eu d)).IsNegInvariant := inferInstance

local instance instEMN (d : ℕ) : MeasurableNeg (Eu d) := inferInstance

/-- Hypotheses on a kernel family `K t x y` (time `t > 0`) with `x`-derivatives `K1 K2 K3`
and Gaussian bounds on the convex set `S`. -/
structure KHyp (d : ℕ) (S : Set (Eu d)) (K : ℝ → Eu d → Eu d → ℝ)
    (K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ))
    (K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ))
    (K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)) (A c : ℝ) : Prop where
  hA : 0 ≤ A
  hc : 0 < c
  hS : MeasurableSet S
  hconv : Convex ℝ S
  d1 : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K t x y) (K1 t x y) x
  d2 : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K1 t x y) (K2 t x y) x
  d3 : ∀ t, 0 < t → ∀ x y, HasFDerivAt (fun x => K2 t x y) (K3 t x y) x
  b0 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, |K t x y| ≤ A * G d (c * t) (x - y)
  b1 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * G d (c * t) (x - y)
  b2 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * G d (c * t) (x - y)
  b3 : ∀ t, 0 < t → ∀ x ∈ S, ∀ y ∈ S, ‖K3 t x y‖ ≤ A * t ^ (-(3 / 2 : ℝ)) * G d (c * t) (x - y)
  m0 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K p.1 x p.2)
  m1 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K1 p.1 x p.2)
  m2 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K2 p.1 x p.2)
  m3 : ∀ x, StronglyMeasurable (fun p : ℝ × Eu d => K3 p.1 x p.2)
  dom : ∀ t, 0 < t → ∀ x₀ : Eu d, ∃ r : ℝ, 0 < r ∧ ∃ F : Eu d → ℝ, IntegrableOn F S ∧
    ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ S, |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧
      ‖K2 t x y‖ ≤ F y ∧ ‖K3 t x y‖ ≤ F y
  heat : ∀ t, 0 < t → ∀ x y, HasDerivAt (fun t => K t x y)
    ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t
  mass : ∀ t, 0 < t → ∀ x, ∫ y in S, K t x y = 1

section KernelInt

variable {d : ℕ} {S : Set (Eu d)} {K : ℝ → Eu d → Eu d → ℝ}
  {K1 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] ℝ)}
  {K2 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)}
  {K3 : ℝ → Eu d → Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ)} {A c : ℝ}

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

/-- Trace of a bilinear form in the standard basis (twice the generator `Δ/2` acts as `lap2/2`). -/
noncomputable def lap2 {d : ℕ} (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : ℝ :=
  ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

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

section HalfGeom

variable {d : ℕ}

end HalfGeom

section GDeriv4

variable {d : ℕ}

noncomputable local instance instL2N7 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S7 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N7 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S7 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end GDeriv4

section GDeriv4b

variable {d : ℕ}

noncomputable local instance instL2N7b (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S7b (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N7b (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S7b (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end GDeriv4b

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
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
theorem wholeKHyp (d : ℕ) [IFacts d] : KHyp d univ (wK d) wK1 wK2 wK3 (wA d) 4 where
  hA := wA_nonneg
  hc := by norm_num
  hS := MeasurableSet.univ
  hconv := convex_univ
  d1 := fun t _ x y => wK_d1 t x y
  d2 := fun t _ x y => wK_d2 t x y
  d3 := fun t _ x y => wK_d3 t x y
  b0 := fun t ht x _ y _ => (whole_bounds ht x y).1
  b1 := fun t ht x _ y _ => (whole_bounds ht x y).2.1
  b2 := fun t ht x _ y _ => (whole_bounds ht x y).2.2.1
  b3 := fun t ht x _ y _ => (whole_bounds ht x y).2.2.2
  m0 := fun x => by
    rw [show (fun p : ℝ × Eu d => wK d p.1 x p.2) = fun p => hN d p.1 * ge d (1 / (2 * p.1)) (x - p.2)
      from funext fun p => wK_eq p.1 x p.2]
    exact sm_hN.mul ((contDiff_ge_uncurry (d := d)).continuous.comp_stronglyMeasurable (sm_T x))
  m1 := fun x => sm_hN.smul (continuous_gK1_uncurry.comp_stronglyMeasurable (sm_T x))
  m2 := fun x => sm_hN.smul (contDiff_gK2_uncurry.continuous.comp_stronglyMeasurable (sm_T x))
  m3 := fun x => sm_hN.smul (continuous_gK3_uncurry.comp_stronglyMeasurable (sm_T x))
  dom := fun t ht x₀ => by
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
  heat := fun t ht x y => wK_heat ht x y
  mass := fun t ht x => wK_mass ht x

lemma whole_meas (x : Eu d) :
    StronglyMeasurable (fun p : ℝ × Eu d => wK d p.1 x p.2) ∧
    StronglyMeasurable (fun p : ℝ × Eu d => wK1 p.1 x p.2) ∧
    StronglyMeasurable (fun p : ℝ × Eu d => wK2 p.1 x p.2) ∧
    StronglyMeasurable (fun p : ℝ × Eu d => wK3 p.1 x p.2) :=
  ⟨(wholeKHyp d).m0 x, (wholeKHyp d).m1 x, (wholeKHyp d).m2 x, (wholeKHyp d).m3 x⟩

end Whole2

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
  let lap2 : {d : ℕ} → (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → ℝ := fun {d : ℕ} (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) => (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1));
    (ContDiff ℝ ⊤ (fun p : ℝ × EuclideanSpace ℝ (Fin d) => gK2 p.1 p.2)) ∧
    (Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => gK1 p.1 p.2)) ∧
    (Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => gK3 p.1 p.2)) ∧
    (StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => hN p.1)) ∧
    (∀ (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)), wK t x y = hN t * ge (1 / (2 * t)) (x - y)) ∧
    (∀ {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), lap2 (wK2 t x y) = G (2 * t) (x - y) * (‖x - y‖ ^ 2 / t ^ 2 - d / t)) ∧
    (∀ {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), HasDerivAt (fun t => wK t x y) ((1 / 2 : ℝ) * lap2 (wK2 t x y)) t) ∧
    (∀ (x : EuclideanSpace ℝ (Fin d)), StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => wK p.1 x p.2) ∧ StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => wK1 p.1 x p.2) ∧ StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => wK2 p.1 x p.2) ∧ StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => wK3 p.1 x p.2)) := by
  intro d
  intro G Ip ge gK1 gK2 gK3 hN wK wK1 wK2 wK3 lap2
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  haveI : ObliqueLib.IFacts d := ⟨f_gK2_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_ge, f_wA_nonneg, f_whole_bounds⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact @ObliqueLib.contDiff_gK2_uncurry d _
  · exact @ObliqueLib.continuous_gK1_uncurry d _
  · exact @ObliqueLib.continuous_gK3_uncurry d _
  · exact @ObliqueLib.sm_hN d _
  · exact (fun t x y => @ObliqueLib.wK_eq d _ t x y)
  · exact (fun {t} ht x y => @ObliqueLib.wK2_trace d _ t ht x y)
  · exact (fun {t} ht x y => @ObliqueLib.wK_heat d _ t ht x y)
  · exact (fun x => @ObliqueLib.whole_meas d _ x)
