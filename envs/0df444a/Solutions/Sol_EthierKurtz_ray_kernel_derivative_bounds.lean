-- Prove2me | solution 1 for EthierKurtz.ray_kernel_derivative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T13:43:36.504157+00:00
-- url     : https://prove2.me/submissions/dcb737a0-ff57-4b6c-9b28-806171ee1ff5

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_heat_kernel_calculus
import Theorems.Thm_EthierKurtz_gaussian_fourth_derivative_bound
import Theorems.Thm_EthierKurtz_ray_integrand_derivative_bounds

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology

namespace ObliqueLib
/-- Euclidean space of dimension `d`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Normalized Gaussian of "variance parameter" `s`: `G s z = (π s)^(-d/2) exp(-|z|^2/s)`. -/
noncomputable def G (d : ℕ) (s : ℝ) (z : Eu d) : ℝ :=
  (π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s)

lemma G_pos {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 < G d s z :=
  mul_pos (rpow_pos_of_pos (mul_pos pi_pos hs) _) (exp_pos _)

lemma G_nonneg {d : ℕ} {s : ℝ} (hs : 0 < s) (z : Eu d) : 0 ≤ G d s z := (G_pos hs z).le

lemma continuous_G {d : ℕ} (s : ℝ) : Continuous (G d s) := by
  unfold G; fun_prop

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

section IFk

variable {d : ℕ}

class IFacts (d : ℕ) : Prop where
  wA_nonneg : 0 ≤ wA d
  inner_Rf : ∀ {e : Eu d} (he : ‖e‖ = 1) (x : Eu d), inner ℝ (Rf e x) e = -inner ℝ x e
  G_Rf_le : ∀ {e : Eu d} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) {x y : Eu d} (hx : 0 ≤ inner ℝ x e) (hy : 0 ≤ inner ℝ y e), G d s (x - Rf e y) ≤ G d s (x - y)
  rK_pos : ∀ (b : Eu d), 0 < rK b
  G_ray_le : ∀ {e b z : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {m s σ : ℝ} (hm : 0 ≤ m) (hz : -m ≤ inner ℝ z e) (hs : 0 ≤ s) (hσ : 0 < σ), G d σ (z + s • (e - b)) ≤ rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * G d (rK b * σ) z * rexp (-(1 / (rK b * σ)) * s ^ 2)
  contDiff_gK3 : ∀ (a : ℝ), ContDiff ℝ ⊤ (gK3 (d := d) a)
  rP_d0 : ∀ (b : Eu d) (t : ℝ) (w : Eu d), HasFDerivAt (rP0 b t) (rP1 b t w) w
  rP_d1 : ∀ (b : Eu d) (t : ℝ) (w : Eu d), HasFDerivAt (rP1 b t) (rP2 b t w) w
  rP_d2 : ∀ (b : Eu d) (t : ℝ) (w : Eu d), HasFDerivAt (rP2 b t) (rP3 b t w) w
  rP_bounds : ∀ (b : Eu d) {t : ℝ} (ht : 0 < t) (w : Eu d), |rP0 b t w| ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) w ∧ ‖rP1 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 : ℝ)) * G d (4 * t) w ∧ ‖rP2 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(3 / 2 : ℝ)) * G d (4 * t) w ∧ ‖rP3 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(2 : ℝ)) * G d (4 * t) w

end IFk

export IFacts (wA_nonneg inner_Rf G_Rf_le rK_pos G_ray_le contDiff_gK3 rP_d0 rP_d1 rP_d2 rP_bounds)

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

section RayK

variable {d : ℕ}

variable [IFacts d]

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

lemma hasFDerivAt_sub_add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Eu d → F}
    {f' : Eu d → (Eu d →L[ℝ] F)} (hf : ∀ w, HasFDerivAt f (f' w) w) (c p x : Eu d) :
    HasFDerivAt (fun x => f (x - c + p)) (f' (x - c + p)) x := by
  have h := (hf (x - c + p)).comp x (((hasFDerivAt_id x).sub_const c).add_const p)
  rwa [ContinuousLinearMap.comp_id] at h

lemma continuous_rP3 (b : Eu d) (t : ℝ) : Continuous (rP3 b t) := by
  have h : Continuous (gK4 (d := d) (1 / (2 * t))) :=
    (contDiff_gK3 (d := d) (1 / (2 * t))).continuous_fderiv (by simp)
  exact (continuous_const.clm_comp h).const_smul (hN d t)

lemma continuous_rP2 (b : Eu d) (t : ℝ) : Continuous (rP2 b t) :=
  continuous_iff_continuousAt.2 fun w => (rP_d2 b t w).continuousAt

lemma continuous_rP1 (b : Eu d) (t : ℝ) : Continuous (rP1 b t) :=
  continuous_iff_continuousAt.2 fun w => (rP_d1 b t w).continuousAt

lemma continuous_rP0 (b : Eu d) (t : ℝ) : Continuous (rP0 b t) :=
  continuous_iff_continuousAt.2 fun w => (rP_d0 b t w).continuousAt

noncomputable def rk0 (e b : Eu d) (t : ℝ) (x y : Eu d) : ℝ :=
  ∫ s in Ioi (0 : ℝ), rP0 b t (x - Rf e y + s • (e - b))

noncomputable def rk1 (e b : Eu d) (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] ℝ :=
  ∫ s in Ioi (0 : ℝ), rP1 b t (x - Rf e y + s • (e - b))

noncomputable def rk2 (e b : Eu d) (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ s in Ioi (0 : ℝ), rP2 b t (x - Rf e y + s • (e - b))

noncomputable def rk3 (e b : Eu d) (t : ℝ) (x y : Eu d) : Eu d →L[ℝ] Eu d →L[ℝ] Eu d →L[ℝ] ℝ :=
  ∫ s in Ioi (0 : ℝ), rP3 b t (x - Rf e y + s • (e - b))

/-- Differentiation under the ray integral. -/
lemma ray_hasFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {σ M M' : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M)
    (hM' : 0 ≤ M') {f : Eu d → F} {f' : Eu d → (Eu d →L[ℝ] F)}
    (hf : ∀ w, HasFDerivAt f (f' w) w) (hf'c : Continuous f')
    (hfb : ∀ w, ‖f w‖ ≤ M * G d σ w) (hf'b : ∀ w, ‖f' w‖ ≤ M' * G d σ w) (c x : Eu d) :
    HasFDerivAt (fun x => ∫ s in Ioi (0 : ℝ), f (x - c + s • (e - b)))
      (∫ s in Ioi (0 : ℝ), f' (x - c + s • (e - b))) x := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun w => (hf w).continuousAt
  have hm : ∀ z : Eu d, -|inner ℝ z e| ≤ inner ℝ z e := fun z => neg_abs_le _
  have hlin : ∀ x' : Eu d, Continuous (fun s : ℝ => x' - c + s • (e - b)) := fun x' =>
    continuous_const.add (continuous_id.smul continuous_const)
  have hGi := (ray_integral_bound (F := ℝ) he hb (abs_nonneg _) (hm (x - c))
    (by positivity : 0 < 2 * σ) zero_le_one (φ := G d (2 * σ)) (continuous_G (2 * σ))
    (fun w => by rw [Real.norm_of_nonneg (G_nonneg (by positivity) w), one_mul])).1
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun x s => f (x - c + s • (e - b))) (F' := fun x s => f' (x - c + s • (e - b)))
    (bound := fun s => M' * (rexp (1 / σ) * 2 ^ ((d : ℝ) / 2)) * G d (2 * σ) (x - c + s • (e - b)))
    (Metric.ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x' => (hfc.comp (hlin x')).aestronglyMeasurable
  · exact (ray_integral_bound he hb (abs_nonneg _) (hm (x - c)) hσ hM hfc hfb).1
  · exact (hf'c.comp (hlin x)).aestronglyMeasurable
  · refine Eventually.of_forall fun s x' hx' => ?_
    have hx'' : ‖x' - x‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hx'
    have h1 := G_shift_le (d := d) hσ (y := c - s • (e - b)) hx''
    have e1 : x' - (c - s • (e - b)) = x' - c + s • (e - b) := by abel
    have e2 : x - (c - s • (e - b)) = x - c + s • (e - b) := by abel
    rw [e1, e2] at h1
    calc ‖f' (x' - c + s • (e - b))‖ ≤ M' * G d σ (x' - c + s • (e - b)) := hf'b _
      _ ≤ M' * (rexp (1 / σ) * 2 ^ ((d : ℝ) / 2) * G d (2 * σ) (x - c + s • (e - b))) :=
          mul_le_mul_of_nonneg_left h1 hM'
      _ = _ := by ring
  · exact hGi.const_mul _
  · exact Eventually.of_forall fun s x' _ => hasFDerivAt_sub_add hf c (s • (e - b)) x'

lemma rP_b0 (b : Eu d) {t : ℝ} (ht : 0 < t) (w : Eu d) :
    ‖rP0 b t w‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * G d (4 * t) w := by
  rw [Real.norm_eq_abs]; exact (rP_bounds b ht w).1

lemma rP_const_nonneg (b : Eu d) {t : ℝ} (ht : 0 < t) (p : ℝ) :
    0 ≤ ‖b‖ * (2 * wA d) * t ^ p := by
  have := wA_nonneg (d := d); have := rpow_nonneg ht.le p; positivity

lemma rk_d0 {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : Eu d) :
    HasFDerivAt (fun x => rk0 e b t x y) (rk1 e b t x y) x :=
  ray_hasFDerivAt he hb (by positivity : 0 < 4 * t) (rP_const_nonneg b ht _)
    (rP_const_nonneg b ht _) (rP_d0 b t) (continuous_rP1 b t) (rP_b0 b ht)
    (fun w => (rP_bounds b ht w).2.1) (Rf e y) x

lemma rk_d1 {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : Eu d) :
    HasFDerivAt (fun x => rk1 e b t x y) (rk2 e b t x y) x :=
  ray_hasFDerivAt he hb (by positivity : 0 < 4 * t) (rP_const_nonneg b ht _)
    (rP_const_nonneg b ht _) (rP_d1 b t) (continuous_rP2 b t) (fun w => (rP_bounds b ht w).2.1)
    (fun w => (rP_bounds b ht w).2.2.1) (Rf e y) x

lemma rk_d2 {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : Eu d) :
    HasFDerivAt (fun x => rk2 e b t x y) (rk3 e b t x y) x :=
  ray_hasFDerivAt he hb (by positivity : 0 < 4 * t) (rP_const_nonneg b ht _)
    (rP_const_nonneg b ht _) (rP_d2 b t) (continuous_rP3 b t) (fun w => (rP_bounds b ht w).2.2.1)
    (fun w => (rP_bounds b ht w).2.2.2) (Rf e y) x

/-- Gaussian bounds of the ray kernel when `⟪x - Rf e y, e⟫ ≥ -m`. -/
lemma rk_bounds_gen {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t m : ℝ} (ht : 0 < t)
    (hm : 0 ≤ m) {x y : Eu d} (hxy : -m ≤ inner ℝ (x - Rf e y) e) :
    |rk0 e b t x y| ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 / 2 : ℝ)) * rC d b m (4 * t) *
        G d (rK b * (4 * t)) (x - Rf e y) ∧
    ‖rk1 e b t x y‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(1 : ℝ)) * rC d b m (4 * t) *
        G d (rK b * (4 * t)) (x - Rf e y) ∧
    ‖rk2 e b t x y‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(3 / 2 : ℝ)) * rC d b m (4 * t) *
        G d (rK b * (4 * t)) (x - Rf e y) ∧
    ‖rk3 e b t x y‖ ≤ ‖b‖ * (2 * wA d) * t ^ (-(2 : ℝ)) * rC d b m (4 * t) *
        G d (rK b * (4 * t)) (x - Rf e y) := by
  have h4 : 0 < 4 * t := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.norm_eq_abs]
    exact (ray_integral_bound he hb hm hxy h4 (rP_const_nonneg b ht _) (continuous_rP0 b t)
      (rP_b0 b ht)).2
  · exact (ray_integral_bound he hb hm hxy h4 (rP_const_nonneg b ht _) (continuous_rP1 b t)
      (fun w => (rP_bounds b ht w).2.1)).2
  · exact (ray_integral_bound he hb hm hxy h4 (rP_const_nonneg b ht _) (continuous_rP2 b t)
      (fun w => (rP_bounds b ht w).2.2.1)).2
  · exact (ray_integral_bound he hb hm hxy h4 (rP_const_nonneg b ht _) (continuous_rP3 b t)
      (fun w => (rP_bounds b ht w).2.2.2)).2

/-- `rC` at `m = 0`, `σ = 4t`, as a multiple of `√t`. -/
noncomputable def rB (d : ℕ) (b : Eu d) : ℝ := rK b ^ ((d : ℝ) / 2) * (√(π * (rK b * 4)) / 2)

lemma rB_nonneg (b : Eu d) : 0 ≤ rB d b := by have := rK_pos b; unfold rB; positivity

lemma rC_zero (b : Eu d) {t : ℝ} (ht : 0 < t) : rC d b 0 (4 * t) = rB d b * t ^ (1 / 2 : ℝ) := by
  unfold rC rB
  rw [show π * (rK b * (4 * t)) = π * (rK b * 4) * t by ring,
    Real.sqrt_mul (by have := rK_pos b; positivity), Real.sqrt_eq_rpow t]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, exp_zero, mul_one]
  ring

/-- The ray-kernel constant on the half-space. -/
noncomputable def rA (d : ℕ) (b : Eu d) : ℝ := ‖b‖ * (2 * wA d) * rB d b

lemma rA_nonneg (b : Eu d) : 0 ≤ rA d b := by
  have := wA_nonneg (d := d); have := rB_nonneg b; unfold rA; positivity

lemma rpow_half_mul {t p : ℝ} (ht : 0 < t) : t ^ (p - 1 / 2) * t ^ (1 / 2 : ℝ) = t ^ p := by
  rw [← rpow_add ht]; congr 1; ring

/-- Gaussian bounds of the ray kernel on the half-space `⟪·, e⟫ ≥ 0`. -/
lemma rk_bounds {e b : Eu d} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t)
    {x y : Eu d} (hx : 0 ≤ inner ℝ x e) (hy : 0 ≤ inner ℝ y e) :
    |rk0 e b t x y| ≤ rA d b * G d (rK b * (4 * t)) (x - y) ∧
    ‖rk1 e b t x y‖ ≤ rA d b * t ^ (-(1 / 2 : ℝ)) * G d (rK b * (4 * t)) (x - y) ∧
    ‖rk2 e b t x y‖ ≤ rA d b * t ^ (-(1 : ℝ)) * G d (rK b * (4 * t)) (x - y) ∧
    ‖rk3 e b t x y‖ ≤ rA d b * t ^ (-(3 / 2 : ℝ)) * G d (rK b * (4 * t)) (x - y) := by
  have hxy : -0 ≤ inner ℝ (x - Rf e y) e := by
    rw [inner_sub_left, inner_Rf he]; linarith
  obtain ⟨c0, c1, c2, c3⟩ := rk_bounds_gen he hb ht le_rfl hxy
  have hG := G_Rf_le (d := d) he (by have := rK_pos b; positivity : 0 < rK b * (4 * t)) hx hy
  rw [rC_zero b ht] at c0 c1 c2 c3
  have hA := rA_nonneg (d := d) b
  have key : ∀ p q : ℝ, q - 1 / 2 = p → ∀ X : ℝ,
      X ≤ ‖b‖ * (2 * wA d) * t ^ p * (rB d b * t ^ (1 / 2 : ℝ)) * G d (rK b * (4 * t)) (x - Rf e y) →
      X ≤ rA d b * t ^ q * G d (rK b * (4 * t)) (x - y) := by
    intro p q hpq X hX
    refine hX.trans ?_
    have e1 : ‖b‖ * (2 * wA d) * t ^ p * (rB d b * t ^ (1 / 2 : ℝ)) = rA d b * t ^ q := by
      rw [← hpq, ← rpow_half_mul (p := q) ht, rA]; ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left hG (mul_nonneg hA (rpow_nonneg ht.le _))
  refine ⟨?_, key _ _ (by norm_num) _ c1, key _ _ (by norm_num) _ c2, key _ _ (by norm_num) _ c3⟩
  have := key (-(1 / 2 : ℝ)) 0 (by norm_num) _ c0
  rwa [rpow_zero, mul_one] at this

end RayK

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
  let wA : ℝ := (51 * 2 ^ ((d : ℝ) / 2));
  let Rf : (e x : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) := fun (e x : EuclideanSpace ℝ (Fin d)) => (x - (2 * inner ℝ x e) • e);
  let rK : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (14 + 8 * ‖b‖ ^ 2);
  let rC : (b : EuclideanSpace ℝ (Fin d)) → (m σ : ℝ) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (m σ : ℝ) => (rK b ^ ((d : ℝ) / 2) * rexp (m ^ 2 / σ) * (√(π * (rK b * σ)) / 2));
  let gK4 : (a : ℝ) → (z : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (a : ℝ) (z : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (gK3 a) z);
  let eb1 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.apply ℝ ℝ b);
  let eb2 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) ℝ (eb1 b));
  let eb3 : (b : EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun (b : EuclideanSpace ℝ (Fin d)) => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (eb2 b));
  let rP0 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t * eb1 b (gK1 (1 / (2 * t)) w));
  let rP1 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb2 b (gK2 (1 / (2 * t)) w));
  let rP2 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • eb3 b (gK3 (1 / (2 * t)) w));
  let rP3 : (b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (w : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) => (hN t • (eb3 b).comp (gK4 (1 / (2 * t)) w));
  let rk0 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP0 b t (x - Rf e y + s • (e - b)));
  let rk1 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP1 b t (x - Rf e y + s • (e - b)));
  let rk2 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP2 b t (x - Rf e y + s • (e - b)));
  let rk3 : (e b : EuclideanSpace ℝ (Fin d)) → (t : ℝ) → (x y : EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun (e b : EuclideanSpace ℝ (Fin d)) (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => (∫ s in Ioi (0 : ℝ), rP3 b t (x - Rf e y + s • (e - b)));
  let rB : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (rK b ^ ((d : ℝ) / 2) * (√(π * (rK b * 4)) / 2));
  let rA : (b : EuclideanSpace ℝ (Fin d)) → ℝ := fun (b : EuclideanSpace ℝ (Fin d)) => (‖b‖ * (2 * wA) * rB b);
    (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ), Continuous (rP2 b t)) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ), Continuous (rP1 b t)) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) (t : ℝ), Continuous (rP0 b t)) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t) (w : EuclideanSpace ℝ (Fin d)), ‖rP0 b t w‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(1 / 2 : ℝ)) * G (4 * t) w) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t) (p : ℝ), 0 ≤ ‖b‖ * (2 * wA) * t ^ p) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => rk0 e b t x y) (rk1 e b t x y) x) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => rk1 e b t x y) (rk2 e b t x y) x) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) (x y : EuclideanSpace ℝ (Fin d)), HasFDerivAt (fun x => rk2 e b t x y) (rk3 e b t x y) x) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t m : ℝ} (ht : 0 < t) (hm : 0 ≤ m) {x y : EuclideanSpace ℝ (Fin d)} (hxy : -m ≤ inner ℝ (x - Rf e y) e), |rk0 e b t x y| ≤ ‖b‖ * (2 * wA) * t ^ (-(1 / 2 : ℝ)) * rC b m (4 * t) * G (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk1 e b t x y‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(1 : ℝ)) * rC b m (4 * t) * G (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk2 e b t x y‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(3 / 2 : ℝ)) * rC b m (4 * t) * G (rK b * (4 * t)) (x - Rf e y) ∧ ‖rk3 e b t x y‖ ≤ ‖b‖ * (2 * wA) * t ^ (-(2 : ℝ)) * rC b m (4 * t) * G (rK b * (4 * t)) (x - Rf e y)) ∧
    (∀ (b : EuclideanSpace ℝ (Fin d)), 0 ≤ rA b) ∧
    (∀ {e b : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) (hb : inner ℝ b e = 0) {t : ℝ} (ht : 0 < t) {x y : EuclideanSpace ℝ (Fin d)} (hx : 0 ≤ inner ℝ x e) (hy : 0 ≤ inner ℝ y e), |rk0 e b t x y| ≤ rA b * G (rK b * (4 * t)) (x - y) ∧ ‖rk1 e b t x y‖ ≤ rA b * t ^ (-(1 / 2 : ℝ)) * G (rK b * (4 * t)) (x - y) ∧ ‖rk2 e b t x y‖ ≤ rA b * t ^ (-(1 : ℝ)) * G (rK b * (4 * t)) (x - y) ∧ ‖rk3 e b t x y‖ ≤ rA b * t ^ (-(3 / 2 : ℝ)) * G (rK b * (4 * t)) (x - y)) := by
  intro d
  intro G Ip ge gK1 gK2 gK3 hN wA Rf rK rC gK4 eb1 eb2 eb3 rP0 rP1 rP2 rP3 rk0 rk1 rk2 rk3 rB rA
  obtain ⟨f_ge_pos, f_gK1_apply, f_gK2_apply, f_hasFDerivAt_ge, f_hasFDerivAt_gK1, f_contDiff_gK2, f_hasFDerivAt_gK2, f_gK3_apply, f_G_eq_ge, f_wK_d1, f_wK_d2, f_wK_d3, f_hN_pos, f_hN_ge, f_wA_nonneg, f_whole_bounds, f_inner_self_unit, f_inner_Rf, f_norm_sub_Rf_sq, f_G_Rf_le, f_G_mono_s, f_one_le_rK, f_rK_pos, f_G_ray_le, f_rC_nonneg⟩ := @EthierKurtz.gaussian_heat_kernel_calculus d
  obtain ⟨f_contDiff_gK3, f_hasFDerivAt_gK3, f_whole_bound4⟩ := @EthierKurtz.gaussian_fourth_derivative_bound d
  obtain ⟨f_eb1_apply, f_rP_d0, f_rP_d1, f_rP_d2, f_rP_bounds⟩ := @EthierKurtz.ray_integrand_derivative_bounds d
  haveI : ObliqueLib.IFacts d := ⟨f_wA_nonneg, f_inner_Rf, f_G_Rf_le, f_rK_pos, f_G_ray_le, f_contDiff_gK3, f_rP_d0, f_rP_d1, f_rP_d2, f_rP_bounds⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fun b t => @ObliqueLib.continuous_rP2 d _ b t)
  · exact (fun b t => @ObliqueLib.continuous_rP1 d _ b t)
  · exact (fun b t => @ObliqueLib.continuous_rP0 d _ b t)
  · exact (fun b {t} ht w => @ObliqueLib.rP_b0 d _ b t ht w)
  · exact (fun b {t} ht p => @ObliqueLib.rP_const_nonneg d _ b t ht p)
  · exact (fun {e b} he hb {t} ht x y => @ObliqueLib.rk_d0 d _ e b he hb t ht x y)
  · exact (fun {e b} he hb {t} ht x y => @ObliqueLib.rk_d1 d _ e b he hb t ht x y)
  · exact (fun {e b} he hb {t} ht x y => @ObliqueLib.rk_d2 d _ e b he hb t ht x y)
  · exact (fun {e b} he hb {t m} ht hm {x y} hxy => @ObliqueLib.rk_bounds_gen d _ e b he hb t m ht hm x y hxy)
  · exact (fun b => @ObliqueLib.rA_nonneg d _ b)
  · exact (fun {e b} he hb {t} ht {x y} hx hy => @ObliqueLib.rk_bounds d _ e b he hb t ht x y hx hy)
