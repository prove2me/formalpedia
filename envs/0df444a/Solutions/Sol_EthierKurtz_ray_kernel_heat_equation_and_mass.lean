-- Prove2me | solution 1 for EthierKurtz.ray_kernel_heat_equation_and_mass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T14:17:33.875986+00:00
-- url     : https://prove2.me/submissions/a1766e11-127c-4593-bc49-f5aa3a2aae4b

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_heat_kernel_solves_heat_equation
import Theorems.Thm_EthierKurtz_ray_integrand_derivative_bounds
import Theorems.Thm_EthierKurtz_ray_kernel_derivative_bounds

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

section Whole2

variable {d : ℕ}

noncomputable local instance instL2N6 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S6 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end Whole2

section HalfGeom

variable {d : ℕ}

/-- Reflection across the hyperplane `⟪x, e⟫ = 0`. -/
noncomputable def Rf (e x : Eu d) : Eu d := x - (2 * inner ℝ x e) • e

/-- The constant of the ray lower bound. -/
noncomputable def rK (b : Eu d) : ℝ := 14 + 8 * ‖b‖ ^ 2

/-- The constant of the ray integral. -/
noncomputable def rC (d : ℕ) (b : Eu d) (m σ : ℝ) : ℝ :=
  rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * (√(π * (rK b * σ)) / 2)

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

noncomputable def gK4 (a : ℝ) (z : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  fderiv ℝ (gK3 a) z

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

noncomputable def eb1 (b : Eu d) : (Eu d →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ b

noncomputable def eb2 (b : Eu d) : (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] (Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.compL ℝ (Eu d) (Eu d →L[ℝ] ℝ) ℝ (eb1 b)

noncomputable def eb3 (b : Eu d) :
    (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.compL ℝ (Eu d) (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (Eu d →L[ℝ] ℝ) (eb2 b)

noncomputable def rP0 (b : Eu d) (t : ℝ) (w : Eu d) : ℝ := hN d t * eb1 b (gK1 (1 / (2 * t)) w)

noncomputable def rP1 (b : Eu d) (t : ℝ) (w : Eu d) : Eu d →L[ℝ] ℝ :=
  hN d t • eb2 b (gK2 (1 / (2 * t)) w)

noncomputable def rP2 (b : Eu d) (t : ℝ) (w : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • eb3 b (gK3 (1 / (2 * t)) w)

noncomputable def rP3 (b : Eu d) (t : ℝ) (w : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  hN d t • (eb3 b).comp (gK4 (1 / (2 * t)) w)

end GDeriv4b

section RayK

variable {d : ℕ}

noncomputable local instance instL2N8 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S8 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N8 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S8 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def rk0 (e b : Eu d) (t : ℝ) (x y : Eu d) : ℝ :=
  ∫ s in Ioi (0 : ℝ), rP0 b t (x - Rf e y + s • (e - b))

noncomputable def rk2 (e b : Eu d) (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ s in Ioi (0 : ℝ), rP2 b t (x - Rf e y + s • (e - b))

end RayK

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  gK1_apply : ∀ (a : ℝ) (z v : Eu d), gK1 a z v = -(2 * a) * ge d a z * inner ℝ z v
  hasFDerivAt_gK1 : ∀ (a : ℝ) (z : Eu d), HasFDerivAt (gK1 a) (gK2 a z) z
  gK3_apply : ∀ (a : ℝ) (z u v w : Eu d), gK3 a z u v w = ge d a z * (-(8 * a ^ 3) * inner ℝ z u * inner ℝ z v * inner ℝ z w + 4 * a ^ 2 * (inner ℝ z u * inner ℝ v w + inner ℝ u v * inner ℝ z w + inner ℝ z v * inner ℝ u w))
  wK_d1 : ∀ (t : ℝ) (x y : Eu d), HasFDerivAt (fun x => wK d t x y) (wK1 t x y) x
  hN_ge : ∀ {t : ℝ} (ht : 0 < t) (z : Eu d), hN d t * ge d (1 / (2 * t)) z = G d (2 * t) z
  wA_nonneg : 0 ≤ wA d
  whole_bounds : ∀ {t : ℝ} (ht : 0 < t) (x y : Eu d), |wK d t x y| ≤ wA d * G d (4 * t) (x - y) ∧ ‖wK1 t x y‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK2 t x y‖ ≤ wA d * t ^ (-(1 : ℝ)) * G d (4 * t) (x - y) ∧ ‖wK3 t x y‖ ≤ wA d * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) (x - y)
  wK_eq : ∀ (t : ℝ) (x y : Eu d), wK d t x y = hN d t * ge d (1 / (2 * t)) (x - y)
  wK2_trace : ∀ {t : ℝ} (ht : 0 < t) (x y : Eu d), lap2 (wK2 t x y) = G d (2 * t) (x - y) * (‖x - y‖ ^ 2 / t ^ 2 - d / t)
  wK_heat : ∀ {t : ℝ} (ht : 0 < t) (x y : Eu d), HasDerivAt (fun t => wK d t x y) ((1 / 2 : ℝ) * lap2 (wK2 t x y)) t
  inner_self_unit : ∀ {e : Eu d} (he : ‖e‖ = 1), inner ℝ e e = (1 : ℝ)
  inner_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1) (x : Eu d), inner ℝ (Rf e x) e = -inner ℝ x e
  norm_sub_Rf_sq : ∀ {e : Eu d} (he : ‖e‖ = 1) (x y : Eu d), ‖x - Rf e y‖ ^ 2 = ‖x - y‖ ^ 2 + 4 * inner ℝ x e * inner ℝ y e
  rK_pos : ∀ (b : Eu d), 0 < rK b
  G_ray_le : ∀ {e b z : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m s σ : ℝ} (hm : 0 ≤ m) (hz : -m ≤ inner ℝ z e) (hs : 0 ≤ s) (hσ : 0 < σ), G d σ (z + s • (e - b)) ≤ rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G d (rK b * σ) z * rexp (-(1 / (rK b * σ)) * s ^ 2)
  eb1_apply : ∀ (b : Eu d) (M : Eu d →L[ℝ] ℝ), eb1 b M = M b
  rP_bounds : ∀ (b : Eu d) {t : ℝ} (ht : 0 < t) (w : Eu d), |rP0 b t w| ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) w ∧ ‖rP1 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 : ℝ)) * G d (4 * t) w ∧ ‖rP2 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) w ∧ ‖rP3 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(2 : ℝ)) * G d (4 * t) w
  continuous_rP2 : ∀ (b : Eu d) (t : ℝ), Continuous (rP2 b t)
  continuous_rP0 : ∀ (b : Eu d) (t : ℝ), Continuous (rP0 b t)
  rP_b0 : ∀ (b : Eu d) {t : ℝ} (ht : 0 < t) (w : Eu d), ‖rP0 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) w
  rP_const_nonneg : ∀ (b : Eu d) {t : ℝ} (ht : 0 < t) (p : ℝ), 0 ≤ ‖b‖ * (2 * wA d) * t ^ p

end IFk

export IFacts (gK1_apply hasFDerivAt_gK1 gK3_apply wK_d1 hN_ge wA_nonneg whole_bounds wK_eq wK2_trace wK_heat inner_self_unit inner_Rf norm_sub_Rf_sq rK_pos G_ray_le eb1_apply rP_bounds continuous_rP2 continuous_rP0 rP_b0 rP_const_nonneg)

section HalfGeom_dup

variable {d : ℕ}

variable [IFacts d]

/-- Integral of a Gaussian-dominated function along the ray `z + s (e - b)`, `s > 0`. -/
lemma ray_integral_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e b z : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m σ M : ℝ} (hm : 0 ≤ m)
    (hz : -m ≤ inner ℝ z e) (hσ : 0 < σ) (hM : 0 ≤ M) {φ : Eu d → F} (hφc : Continuous φ)
    (hφ : ∀ w, ‖φ w‖ ≤ M * G d σ w) :
    IntegrableOn (fun s : ℝ => φ (z + s • (e - b))) (Ioi (0 : ℝ)) ∧
      ‖∫ s in Ioi (0 : ℝ), φ (z + s • (e - b))‖ ≤ M * rC d b m σ * G d (rK b * σ) z := by
  have hK := rK_pos b
  have hKσ : 0 < rK b * σ := mul_pos hK hσ
  set C0 := M * (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G d (rK b * σ) z) with hC0
  have hgi : Integrable (fun s : ℝ => C0 * rexp (-(1 / (rK b * σ)) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul C0
  have hcont : Continuous (fun s : ℝ => φ (z + s • (e - b))) :=
    hφc.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hpt : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖φ (z + s • (e - b))‖ ≤ C0 * rexp (-(1 / (rK b * σ)) * s ^ 2) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
    have h1 := G_ray_le (d := d) he hb hm hz (le_of_lt hs) hσ
    calc ‖φ (z + s • (e - b))‖ ≤ M * G d σ (z + s • (e - b)) := hφ _
      _ ≤ M * (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G d (rK b * σ) z *
            rexp (-(1 / (rK b * σ)) * s ^ 2)) := mul_le_mul_of_nonneg_left h1 hM
      _ = C0 * rexp (-(1 / (rK b * σ)) * s ^ 2) := by rw [hC0]; ring
  refine ⟨hgi.integrableOn.mono' hcont.aestronglyMeasurable hpt, ?_⟩
  calc ‖∫ s in Ioi (0 : ℝ), φ (z + s • (e - b))‖
      ≤ ∫ s in Ioi (0 : ℝ), C0 * rexp (-(1 / (rK b * σ)) * s ^ 2) :=
        norm_integral_le_of_norm_le hgi.integrableOn hpt
    _ = C0 * (√(π / (1 / (rK b * σ))) / 2) := by rw [integral_const_mul, integral_gaussian_Ioi]
    _ = M * rC d b m σ * G d (rK b * σ) z := by
        rw [hC0, rC, show π / (1 / (rK b * σ)) = π * (rK b * σ) by field_simp]; ring

end HalfGeom_dup

section RayHeat

variable {d : ℕ}

variable [IFacts d]

noncomputable local instance instL2N9 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S9 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance instL3N9 (d : ℕ) :
    NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL3S9 (d : ℕ) :
    NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

lemma inner_eq_sum (z b : Eu d) : inner ℝ z b = ∑ i, z i * b i := by
  simp [PiLp.inner_apply, mul_comm]

lemma sum_gK3_b (a : ℝ) (z b : Eu d) :
    ∑ i, gK3 a z (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) b
      = ge d a z * inner ℝ z b * (-(8 * a ^ 3) * ‖z‖ ^ 2 + 4 * a ^ 2 * (d + 2)) := by
  have hs : ∀ i, inner ℝ z (EuclideanSpace.single i (1 : ℝ)) = z i := by
    intro i; simp [EuclideanSpace.inner_single_right]
  have hl : ∀ i, inner ℝ (EuclideanSpace.single i (1 : ℝ)) b = b i := by
    intro i; simp [EuclideanSpace.inner_single_left]
  have h1 : ∀ i : Fin d, inner ℝ (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) = 1 := by
    intro i; simp [EuclideanSpace.inner_single_right]
  have hpt : ∀ i, gK3 a z (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) b
      = (ge d a z * (-(8 * a ^ 3)) * inner ℝ z b) * (z i ^ 2)
        + (ge d a z * (8 * a ^ 2)) * (z i * b i) + ge d a z * (4 * a ^ 2) * inner ℝ z b := by
    intro i; rw [gK3_apply, hs, hl, h1]; ring
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← inner_eq_sum, ← EuclideanSpace.real_norm_sq_eq]
  ring

lemma lap2_rP2 (b : Eu d) (t : ℝ) (w : Eu d) :
    lap2 (rP2 b t w) = hN d t * (ge d (1 / (2 * t)) w * inner ℝ w b *
      (-(8 * (1 / (2 * t)) ^ 3) * ‖w‖ ^ 2 + 4 * (1 / (2 * t)) ^ 2 * (d + 2))) := by
  rw [rP2, lap2_smul]
  congr 1
  exact sum_gK3_b _ w b

lemma rP0_eq (b : Eu d) {t : ℝ} (ht : t ≠ 0) (w : Eu d) :
    rP0 b t w = -t⁻¹ * inner ℝ w b * wK d t w 0 := by
  have h2 : 2 * (1 / (2 * t)) = t⁻¹ := by field_simp
  rw [rP0, eb1_apply, gK1_apply, wK_eq, sub_zero, ← h2]
  ring

/-- Pointwise heat equation for the ray integrand. -/
lemma rP0_heat (b : Eu d) {t : ℝ} (ht : 0 < t) (w : Eu d) :
    HasDerivAt (fun t => rP0 b t w) ((1 / 2 : ℝ) * lap2 (rP2 b t w)) t := by
  have hW := wK_heat (d := d) ht w 0
  have hI : HasDerivAt (fun y : ℝ => -y⁻¹) (-(-(t ^ 2)⁻¹)) t := (hasDerivAt_inv ht.ne').neg
  have hP := (hI.mul_const (inner ℝ w b)).mul hW
  have hev : (fun t => -t⁻¹ * inner ℝ w b * wK d t w 0) =ᶠ[𝓝 t] fun t => rP0 b t w := by
    filter_upwards [lt_mem_nhds ht] with t' ht'
    rw [rP0_eq b ht'.ne']
  refine (hP.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [wK2_trace ht, lap2_rP2, wK, sub_zero]
  have hG : hN d t * ge d (1 / (2 * t)) w = G d (2 * t) w := hN_ge ht w
  rw [show hN d t * (ge d (1 / (2 * t)) w * inner ℝ w b *
      (-(8 * (1 / (2 * t)) ^ 3) * ‖w‖ ^ 2 + 4 * (1 / (2 * t)) ^ 2 * (d + 2)))
      = (hN d t * ge d (1 / (2 * t)) w) * inner ℝ w b *
      (-(8 * (1 / (2 * t)) ^ 3) * ‖w‖ ^ 2 + 4 * (1 / (2 * t)) ^ 2 * (d + 2)) by ring, hG]
  field_simp
  try ring

/-- Heat equation for the ray kernel. -/
lemma rk_heat {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t)
    (x y : Eu d) :
    HasDerivAt (fun t => rk0 e b t x y) ((1 / 2 : ℝ) * lap2 (rk2 e b t x y)) t := by
  set z := x - Rf e y
  set v := e - b
  have hm : -|inner ℝ z e| ≤ inner ℝ z e := neg_abs_le _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlin : Continuous (fun s : ℝ => z + s • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  set C := (1 / 2 : ℝ) * d * (‖b‖ * (2 * wA d) * (t / 2) ^ (-(3 / 2 : ℝ))) *
    (4 : ℝ) ^ ((d : ℝ) / 2) with hC
  have hC0 : 0 ≤ C := by
    have := wA_nonneg (d := d); have := rpow_nonneg (by positivity : (0 : ℝ) ≤ t / 2) (-(3 / 2 : ℝ))
    rw [hC]; positivity
  have hGi := (ray_integral_bound (F := ℝ) he hb (abs_nonneg _) hm
    (by positivity : 0 < 2 * (4 * t)) zero_le_one (φ := G d (2 * (4 * t))) (continuous_G _)
    (fun w => by rw [Real.norm_of_nonneg (G_nonneg (by positivity) w), one_mul])).1
  have hI2 := (ray_integral_bound he hb (abs_nonneg _) hm (by positivity : 0 < 4 * t)
    (rP_const_nonneg b ht _) (continuous_rP2 b t) (fun w => (rP_bounds b ht w).2.2.1)).1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun t s => rP0 b t (z + s • v)) (x₀ := t)
    (F' := fun t s => (1 / 2 : ℝ) * lap2 (rP2 b t (z + s • v)))
    (bound := fun s => C * G d (2 * (4 * t)) (z + s • v))
    (Ioo_mem_nhds (half_lt_self ht) (by linarith : t < 2 * t))
    (Eventually.of_forall fun t' => ((continuous_rP0 b t').comp hlin).aestronglyMeasurable)
    (ray_integral_bound he hb (abs_nonneg _) hm (by positivity : 0 < 4 * t)
      (rP_const_nonneg b ht _) (continuous_rP0 b t) (rP_b0 b ht)).1
    ((continuous_const.mul (continuous_lap2.comp ((continuous_rP2 b t).comp hlin))).aestronglyMeasurable)
    ?_ (hGi.const_mul C) ?_
  · show HasDerivAt (fun n => ∫ s in Ioi (0 : ℝ), rP0 b n (z + s • v)) _ t
    have e : ∫ s in Ioi (0 : ℝ), (1 / 2 : ℝ) * lap2 (rP2 b t (z + s • v))
        = (1 / 2 : ℝ) * lap2 (rk2 e b t x y) := by
      unfold rk2
      rw [lap2_integral hI2, ← integral_const_mul]
    rw [← e]
    exact key.2
  · refine Eventually.of_forall fun s t' ht' => ?_
    have ht'0 : 0 < t' := by linarith [ht'.1, half_pos ht]
    have hG := G_le_near (d := d) (by positivity : 0 < 4 * t) (s' := 4 * t') (by nlinarith [ht'.1])
      (by nlinarith [ht'.2]) (z + s • v)
    have hK2 := (rP_bounds b ht'0 (z + s • v)).2.2.1
    have hpow : t' ^ (-(3 / 2 : ℝ)) ≤ (t / 2) ^ (-(3 / 2 : ℝ)) :=
      rpow_le_rpow_of_nonpos (by positivity) ht'.1.le (by norm_num)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hl := abs_lap2_le (rP2 b t' (z + s • v))
    have hGn := G_nonneg (d := d) (by positivity : 0 < 4 * t') (z + s • v)
    have hW := wA_nonneg (d := d)
    calc 1 / 2 * |lap2 (rP2 b t' (z + s • v))|
        ≤ 1 / 2 * (d * (‖b‖ * (2 * wA d) * t' ^ (-(3 / 2 : ℝ)) * G d (4 * t') (z + s • v))) := by
          gcongr
          exact hl.trans (mul_le_mul_of_nonneg_left hK2 hd)
      _ ≤ 1 / 2 * (d * (‖b‖ * (2 * wA d) * (t / 2) ^ (-(3 / 2 : ℝ)) *
            ((4 : ℝ) ^ ((d : ℝ) / 2) * G d (2 * (4 * t)) (z + s • v)))) := by
          gcongr
      _ = C * G d (2 * (4 * t)) (z + s • v) := by rw [hC]; ring
  · exact Eventually.of_forall fun s t' ht' =>
      rP0_heat b (by linarith [ht'.1, half_pos ht]) (z + s • v)

end RayHeat

section Mass

variable {d : ℕ}

variable [IFacts d]

noncomputable local instance instL2N10 (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2S10 (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The closed half-space `⟪y, e⟫ ≥ 0`. -/
def Hs (e : Eu d) : Set (Eu d) := {y | 0 ≤ inner ℝ y e}

/-- The opposite closed half-space `⟪y, e⟫ ≤ 0`. -/
def Hm (e : Eu d) : Set (Eu d) := {y | inner ℝ y e ≤ 0}

lemma isClosed_Hs (e : Eu d) : IsClosed (Hs e) :=
  isClosed_le continuous_const (continuous_id.inner continuous_const)

lemma isClosed_Hm (e : Eu d) : IsClosed (Hm e) :=
  isClosed_le (continuous_id.inner continuous_const) continuous_const

lemma measurableSet_Hs (e : Eu d) : MeasurableSet (Hs e) := (isClosed_Hs e).measurableSet

lemma measurableSet_Hm (e : Eu d) : MeasurableSet (Hm e) := (isClosed_Hm e).measurableSet

lemma Rf_Rf {e : Eu d} (he : ‖e‖ = 1) (x : Eu d) : Rf e (Rf e x) = x := by
  calc Rf e (Rf e x) = Rf e x - (2 * inner ℝ (Rf e x) e) • e := rfl
    _ = x := by
      rw [inner_Rf he]; simp only [Rf]; rw [mul_neg, neg_smul, sub_neg_eq_add, sub_add_cancel]

lemma norm_Rf {e : Eu d} (he : ‖e‖ = 1) (x : Eu d) : ‖Rf e x‖ = ‖x‖ := by
  have h := norm_sub_Rf_sq he 0 x
  simp only [zero_sub, norm_neg, inner_zero_left, mul_zero, zero_mul, add_zero] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The reflection as a linear isometry equivalence. -/
noncomputable def RfL {e : Eu d} (he : ‖e‖ = 1) : Eu d ≃ₗᵢ[ℝ] Eu d where
  toFun := Rf e
  invFun := Rf e
  map_add' x y := by simp only [Rf, inner_add_left, mul_add, add_smul]; abel
  map_smul' c x := by
    simp only [Rf, real_inner_smul_left, smul_sub, smul_smul, RingHom.id_apply]
    congr 2; ring
  left_inv x := Rf_Rf he x
  right_inv x := Rf_Rf he x
  norm_map' x := norm_Rf he x

lemma continuous_Rf {e : Eu d} (he : ‖e‖ = 1) : Continuous (Rf e) := (RfL he).continuous

lemma Rf_sub_smul {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) (y : Eu d) (τ : ℝ) :
    Rf e (y - τ • b) = Rf e y - τ • b := by
  simp only [Rf, inner_sub_left, real_inner_smul_left, hb]; rw [mul_zero, sub_zero]; abel

lemma Rf_preimage_Hm {e : Eu d} (he : ‖e‖ = 1) : Rf e ⁻¹' Hm e = Hs e := by
  ext y; simp only [Set.mem_preimage, Hm, Hs, Set.mem_setOf_eq, inner_Rf he]; constructor <;>
    intro h <;> linarith

lemma mp_Rf {e : Eu d} (he : ‖e‖ = 1) : MeasurePreserving (Rf e) volume volume :=
  (RfL he).measurePreserving

lemma me_Rf {e : Eu d} (he : ‖e‖ = 1) : MeasurableEmbedding (Rf e) :=
  (RfL he).toHomeomorph.measurableEmbedding

/-- Change of variables `y ↦ Rf e y` on the half-space. -/
lemma setIntegral_Hs_Rf {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {e : Eu d}
    (he : ‖e‖ = 1) (f : Eu d → E') : ∫ y in Hs e, f (Rf e y) = ∫ y in Hm e, f y := by
  rw [← (mp_Rf he).setIntegral_preimage_emb (me_Rf he) f (Hm e), Rf_preimage_Hm he]

lemma integrable_comp_Rf {E' : Type*} [NormedAddCommGroup E'] {e : Eu d} (he : ‖e‖ = 1)
    {f : Eu d → E'} (hf : Integrable f) : Integrable (fun y => f (Rf e y)) :=
  ((mp_Rf he).integrable_comp_emb (me_Rf he)).mpr hf

/-- The boundary hyperplane is null. -/
lemma volume_Hs_inter_Hm {e : Eu d} (he : ‖e‖ = 1) : volume (Hs e ∩ Hm e) = 0 := by
  have hsub : Hs e ∩ Hm e ⊆ ((ℝ ∙ e)ᗮ : Submodule ℝ (Eu d)) := by
    intro y hy
    simp only [Hs, Hm, Set.mem_inter_iff, Set.mem_setOf_eq] at hy
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact le_antisymm hy.2 hy.1
  have hne : (ℝ ∙ e)ᗮ ≠ ⊤ := by
    intro htop
    have : e ∈ (ℝ ∙ e)ᗮ := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_unit he] at this
    exact one_ne_zero this
  exact measure_mono_null hsub (Measure.addHaar_submodule volume _ hne)

/-- `∫_{Hs} f + ∫_{Hm} f = ∫ f`. -/
lemma setIntegral_Hs_add_Hm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {e : Eu d}
    (he : ‖e‖ = 1) {f : Eu d → E'} (hf : Integrable f) :
    (∫ y in Hs e, f y) + ∫ y in Hm e, f y = ∫ y, f y := by
  have hU : Hs e ∪ Hm e = univ := by
    ext y; simp only [Hs, Hm, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total _ _
  have h := integral_union_ae (μ := volume) (f := f) (volume_Hs_inter_Hm he)
    (measurableSet_Hm e).nullMeasurableSet hf.integrableOn hf.integrableOn
  rw [hU, Measure.restrict_univ] at h
  exact h.symm

/-- Mass of the even reflection part. -/
lemma mass_even {e : Eu d} (he : ‖e‖ = 1) {t : ℝ} (ht : 0 < t) (x : Eu d) :
    (∫ y in Hs e, wK d t x y) + ∫ y in Hs e, wK d t x (Rf e y) = 1 := by
  have hf : Integrable (fun y => wK d t x y) := integrable_G_sub (s := 2 * t) (by positivity) x
  rw [setIntegral_Hs_Rf he (fun y => wK d t x y), setIntegral_Hs_add_Hm he hf]
  exact integral_G_sub (s := 2 * t) (by positivity) x

/-- Translation along `b ⊥ e` preserves integrals over the half-space. -/
lemma setIntegral_Hs_shift {e b : Eu d} (hb : inner ℝ b e = 0) (f : Eu d → ℝ) (τ : ℝ) :
    ∫ y in Hs e, f (y - τ • b) = ∫ y in Hs e, f y := by
  rw [← integral_indicator (measurableSet_Hs e), ← integral_indicator (measurableSet_Hs e)]
  have h : (Hs e).indicator (fun y => f (y - τ • b)) = fun y => (Hs e).indicator f (y - τ • b) := by
    funext y
    have hm : y ∈ Hs e ↔ y - τ • b ∈ Hs e := by
      simp only [Hs, Set.mem_setOf_eq, inner_sub_left, real_inner_smul_left, hb, mul_zero, sub_zero]
    classical
    simp only [Set.indicator_apply, hm]
  rw [h, integral_sub_right_eq_self (fun y => (Hs e).indicator f y) (τ • b)]

lemma continuous_wK1 (t : ℝ) (x : Eu d) : Continuous (fun y => wK1 t x y) := by
  have hc : Continuous (gK1 (d := d) (1 / (2 * t))) :=
    continuous_iff_continuousAt.2 fun z => (hasFDerivAt_gK1 (d := d) _ z).continuousAt
  exact (hc.comp (continuous_const.sub continuous_id)).const_smul (hN d t)

/-- The `b`-derivative of the reflected mass vanishes: `∫_{Hs} rP0 b t (w - Rf e y) dy = 0`. -/
lemma mass_ray_inner {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t)
    (w : Eu d) : ∫ y in Hs e, rP0 b t (w - Rf e y) = 0 := by
  have hRc := continuous_Rf he
  have hW := wA_nonneg (d := d)
  set Φ : Eu d → ℝ := fun x => ∫ y in Hs e, (1 : ℝ) • wK d t x (Rf e y) with hΦ
  set C := wA d * (1 + t ^ (-(1 / 2 : ℝ))) * (rexp (1 / (4 * t)) * 2 ^ ((d : ℝ) / 2))
  have hC : 0 ≤ C := by have := rpow_nonneg ht.le (-(1 / 2 : ℝ)); positivity
  have hderiv : ∀ x₀ : Eu d, HasFDerivAt Φ (∫ y in Hs e, (1 : ℝ) • wK1 t x₀ (Rf e y)) x₀ := by
    intro x₀
    refine hasFDerivAt_kint (measurableSet_Hs e) aestronglyMeasurable_const
      (M0 := 1) (fun y _ => by norm_num)
      (fun x => ((continuous_G _).comp ((continuous_const.sub continuous_id).comp hRc)).aestronglyMeasurable)
      (fun x => ((continuous_wK1 t x).comp hRc).aestronglyMeasurable)
      (fun x y => wK_d1 t x (Rf e y)) one_pos
      (F := fun y => C * G d (2 * (4 * t)) (x₀ - Rf e y))
      ((integrable_comp_Rf he ((integrable_G_sub (s := 2 * (4 * t)) (by positivity) x₀).const_mul
        C)).integrableOn)
      ?_ ?_
    · intro x hx y _
      have hx' : ‖x - x₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
      have hsh := G_shift_le (d := d) (by positivity : 0 < 4 * t) (y := Rf e y) hx'
      have b0 := (whole_bounds (d := d) ht x (Rf e y)).1
      rw [Real.norm_eq_abs]
      have := rpow_nonneg ht.le (-(1 / 2 : ℝ))
      have h0 := G_nonneg (d := d) (by positivity : 0 < 4 * t) (x - Rf e y)
      have hX : G d (4 * t) (x - Rf e y) ≤ (1 + t ^ (-(1 / 2 : ℝ))) * (rexp (1 / (4 * t)) *
          2 ^ ((d : ℝ) / 2) * G d (2 * (4 * t)) (x₀ - Rf e y)) := by
        nlinarith [mul_nonneg this (h0.trans hsh)]
      calc |wK d t x (Rf e y)| ≤ wA d * G d (4 * t) (x - Rf e y) := b0
        _ ≤ wA d * ((1 + t ^ (-(1 / 2 : ℝ))) * (rexp (1 / (4 * t)) * 2 ^ ((d : ℝ) / 2) *
              G d (2 * (4 * t)) (x₀ - Rf e y))) := mul_le_mul_of_nonneg_left hX hW
        _ = C * G d (2 * (4 * t)) (x₀ - Rf e y) := by ring
    · intro x hx y _
      have hx' : ‖x - x₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
      have hsh := G_shift_le (d := d) (by positivity : 0 < 4 * t) (y := Rf e y) hx'
      have b1 := (whole_bounds (d := d) ht x (Rf e y)).2.1
      have := rpow_nonneg ht.le (-(1 / 2 : ℝ))
      have hG := G_nonneg (d := d) (by positivity : 0 < 4 * t) (x - Rf e y)
      have hX : t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (x - Rf e y) ≤ (1 + t ^ (-(1 / 2 : ℝ))) *
          (rexp (1 / (4 * t)) * 2 ^ ((d : ℝ) / 2) * G d (2 * (4 * t)) (x₀ - Rf e y)) := by
        nlinarith [mul_le_mul_of_nonneg_left hsh this, hG.trans hsh]
      calc ‖wK1 t x (Rf e y)‖ ≤ wA d * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (x - Rf e y) := b1
        _ = wA d * (t ^ (-(1 / 2 : ℝ)) * G d (4 * t) (x - Rf e y)) := by ring
        _ ≤ wA d * ((1 + t ^ (-(1 / 2 : ℝ))) * (rexp (1 / (4 * t)) * 2 ^ ((d : ℝ) / 2) *
              G d (2 * (4 * t)) (x₀ - Rf e y))) := mul_le_mul_of_nonneg_left hX hW
        _ = C * G d (2 * (4 * t)) (x₀ - Rf e y) := by ring
  -- `Φ` is constant along `b`
  have hconst : ∀ τ : ℝ, Φ (w + τ • b) = Φ w := by
    intro τ
    simp only [hΦ, one_smul]
    have h1 : ∀ y, wK d t (w + τ • b) (Rf e y) = wK d t w (Rf e (y - τ • b)) := by
      intro y; rw [Rf_sub_smul he hb, wK, wK]; congr 1; abel
    simp only [h1]
    exact setIntegral_Hs_shift hb (fun y => wK d t w (Rf e y)) τ
  have hline : HasDerivAt (fun τ : ℝ => w + τ • b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add w
  have hcomp := (hderiv (w + (0 : ℝ) • b)).comp_hasDerivAt (0 : ℝ) hline
  have hfun : (Φ ∘ fun τ : ℝ => w + τ • b) = fun _ => Φ w := funext hconst
  rw [hfun] at hcomp
  have hzero := hcomp.unique (hasDerivAt_const (0 : ℝ) (Φ w))
  rw [zero_smul, add_zero] at hzero
  -- identify the derivative applied to `b` with the integral
  have hint : Integrable (fun y => (1 : ℝ) • wK1 t w (Rf e y)) (volume.restrict (Hs e)) := by
    refine Integrable.mono' ((integrable_comp_Rf he ((integrable_G_sub (s := 4 * t) (by positivity)
      w).const_mul
      (wA d * t ^ (-(1 / 2 : ℝ))))).integrableOn)
      (((continuous_wK1 t w).comp hRc).aestronglyMeasurable.const_smul (1 : ℝ))
      (Eventually.of_forall fun y => ?_)
    rw [one_smul]; exact (whole_bounds (d := d) ht w (Rf e y)).2.1
  rw [ContinuousLinearMap.integral_apply hint] at hzero
  refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans hzero
  simp only [rP0, eb1_apply, wK1, one_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

end Mass

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
  let Rf : (e x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) := fun (e x : EuclideanSpace ℝ (Fin d)) => (x - (2 * inner ℝ x e) • e);
  let eb1 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.apply ℝ ℝ b);
  let eb2 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) ℝ (eb1 b));
  let eb3 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (eb2 b));
  let rP0 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t * eb1 b (gK1 (1 / (2 * t)) w));
  let rP2 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb3 b (gK3 (1 / (2 * t)) w));
  let lap2 : {d : ℕ} → (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → ℝ := fun {d : ℕ} (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) => (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1));
  let rk0 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP0 b t (x - Rf e y + s • (e - b)));
  let rk2 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP2 b t (x - Rf e y + s • (e - b)));
  let Hs : (e : EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d)) := fun (e : EuclideanSpace ℝ (Fin d)) => ({y | 0 ≤ inner ℝ y e});
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), HasDerivAt (fun t => rk0 e b t x y) ((1 / 2 : ℝ) * lap2 (rk2 e b t x y)) t) ∧
    (∀ (e : EuclideanSpace ℝ (Fin d)), MeasurableSet (Hs e)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1), Continuous (Rf e)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1), MeasurePreserving (Rf e) volume volume) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1), MeasurableEmbedding (Rf e)) ∧
    (∀ {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)), (∫ y in Hs e, wK t x y) + ∫ y in Hs e, wK t x (Rf e y) = 1) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (w : EuclideanSpace ℝ (Fin d)), ∫ y in Hs e, rP0 b t (w - Rf e y) = 0) := by
  intro d
  intro G Ip ge gK1 gK2 gK3 hN wK Rf eb1 eb2 eb3 rP0 rP2 lap2 rk0 rk2 Hs
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_contDiff_gK2_uncurry, f_continuous_gK1_uncurry, f_continuous_gK3_uncurry, f_sm_hN, f_wK_eq, f_wK2_trace, f_wK_heat, f_whole_meas⟩ := @EthierKurtz.heat_kernel_solves_heat_equation d
  obtain ⟨f_eb1_apply, f_rP_d0, f_rP_d1, f_rP_d2, f_rP_bounds⟩ := @EthierKurtz.ray_integrand_derivative_bounds d
  obtain ⟨f_continuous_rP2, f_continuous_rP1, f_continuous_rP0, f_rP_b0, f_rP_const_nonneg, f_rk_d0, f_rk_d1, f_rk_d2, f_rk_bounds_gen, f_rA_nonneg, f_rk_bounds⟩ := @EthierKurtz.ray_kernel_derivative_bounds d
  haveI : ObliqueLib.IFacts d := ⟨f_gK1_apply, f_hasFDerivAt_gK1, f_gK3_apply, f_wK_d1, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_wK_eq, f_wK2_trace, f_wK_heat, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_rK_pos, f_G_ray_le, f_eb1_apply, f_rP_bounds, f_continuous_rP2, f_continuous_rP0, f_rP_b0, f_rP_const_nonneg⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fun {e b} he hb {t} ht x y => @ObliqueLib.rk_heat d _ e b he hb t ht x y)
  · exact (fun e => @ObliqueLib.measurableSet_Hs d _ e)
  · exact (fun {e} he => @ObliqueLib.continuous_Rf d _ e he)
  · exact (fun {e} he => @ObliqueLib.mp_Rf d _ e he)
  · exact (fun {e} he => @ObliqueLib.me_Rf d _ e he)
  · exact (fun {e} he {t} ht x => @ObliqueLib.mass_even d _ e he t ht x)
  · exact (fun {e b} he hb {t} ht w => @ObliqueLib.mass_ray_inner d _ e b he hb t ht w)
