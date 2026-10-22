-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_ambient_rotation_bounded_loss
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T04:30:59.630461+00:00
-- url     : https://prove2.me/submissions/a6732d36-f825-43c3-bccc-b9a3917277bc

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open BirkhoffGlobalSection
open scoped ContDiff

set_option autoImplicit false

/-- A function vanishing at `t₀` with positive derivative there is negative just
before `t₀` and positive just after. -/
private lemma sign_near_of_hasDerivAt {f : ℝ → ℝ} {f' t₀ : ℝ}
    (hf : HasDerivAt f f' t₀) (h0 : f t₀ = 0) (hpos : 0 < f') :
    ∃ ε > 0, ∀ s : ℝ, (t₀ < s → s < t₀ + ε → 0 < f s) ∧
      (t₀ - ε < s → s < t₀ → f s < 0) := by
  rw [hasDerivAt_iff_tendsto_slope] at hf
  have hev : ∀ᶠ s in nhdsWithin t₀ {t₀}ᶜ, 0 < slope f t₀ s :=
    hf.eventually (lt_mem_nhds hpos)
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨ε, hε, fun s => ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩⟩
  · have hd : dist s t₀ < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hs := h hd (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; intro he; linarith)
    rw [slope_def_field, h0, sub_zero] at hs
    have hpos' : 0 < s - t₀ := by linarith
    exact (div_pos_iff.mp hs).elim (fun h => h.1) (fun h => absurd h.2 (by linarith))
  · have hd : dist s t₀ < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hs := h hd (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; intro he; linarith)
    rw [slope_def_field, h0, sub_zero] at hs
    exact (div_pos_iff.mp hs).elim (fun h => absurd h.2 (by linarith)) (fun h => h.1)

/-- The same statement for a negative derivative. -/
private lemma sign_near_of_hasDerivAt_neg {f : ℝ → ℝ} {f' t₀ : ℝ}
    (hf : HasDerivAt f f' t₀) (h0 : f t₀ = 0) (hneg : f' < 0) :
    ∃ ε > 0, ∀ s : ℝ, (t₀ < s → s < t₀ + ε → f s < 0) ∧
      (t₀ - ε < s → s < t₀ → 0 < f s) := by
  obtain ⟨ε, hε, h⟩ := sign_near_of_hasDerivAt hf.neg (by simp [h0]) (by linarith)
  refine ⟨ε, hε, fun s => ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩⟩
  · have := (h s).1 h1 h2; simp only [Pi.neg_apply] at this; linarith
  · have := (h s).2 h1 h2; simp only [Pi.neg_apply] at this; linarith

/-- A positive definite binary quadratic form is positive off the origin. -/
private lemma quad_pos {p q r u v : ℝ} (hp : 0 < p) (hdet : 0 < p * r - q ^ 2)
    (huv : u ≠ 0 ∨ v ≠ 0) : 0 < p * u ^ 2 + 2 * q * u * v + r * v ^ 2 := by
  have key : p * (p * u ^ 2 + 2 * q * u * v + r * v ^ 2) =
      (p * u + q * v) ^ 2 + (p * r - q ^ 2) * v ^ 2 := by ring
  rcases huv with hu | hv
  · by_cases hv : v = 0
    · subst hv
      have : 0 < u ^ 2 := by positivity
      nlinarith
    · have : 0 < v ^ 2 := by positivity
      have h2 : 0 < (p * r - q ^ 2) * v ^ 2 := mul_pos hdet this
      have h3 : 0 < p * (p * u ^ 2 + 2 * q * u * v + r * v ^ 2) := by
        rw [key]; nlinarith [sq_nonneg (p * u + q * v)]
      exact pos_of_mul_pos_right h3 hp.le
  · have : 0 < v ^ 2 := by positivity
    have h2 : 0 < (p * r - q ^ 2) * v ^ 2 := mul_pos hdet this
    have h3 : 0 < p * (p * u ^ 2 + 2 * q * u * v + r * v ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (p * u + q * v)]
    exact pos_of_mul_pos_right h3 hp.le

/-- The trace of a rank-one symmetric matrix `N` and the trace of `S N`, for a
positive definite `S`, have the same strict sign. -/
private lemma trace_mul_pos {n00 n01 n11 p q r : ℝ} (hp : 0 < p)
    (hdet : 0 < p * r - q ^ 2) (hrank : n00 * n11 = n01 ^ 2)
    (hne : n00 ≠ 0 ∨ n01 ≠ 0 ∨ n11 ≠ 0) :
    0 < (n00 + n11) * (p * n00 + 2 * q * n01 + r * n11) := by
  have e : (n00 + n11) * (p * n00 + 2 * q * n01 + r * n11) =
      (p * n00 ^ 2 + 2 * q * n00 * n01 + r * n01 ^ 2) +
      (p * n01 ^ 2 + 2 * q * n01 * n11 + r * n11 ^ 2) := by
    have : n00 * n11 = n01 ^ 2 := hrank
    linear_combination (r + p) * this
  rw [e]
  rcases hne with h | h | h
  · have h1 := quad_pos hp hdet (Or.inl h : n00 ≠ 0 ∨ n01 ≠ 0)
    have h2 : 0 ≤ p * n01 ^ 2 + 2 * q * n01 * n11 + r * n11 ^ 2 := by
      by_cases hz : n01 = 0 ∧ n11 = 0
      · rw [hz.1, hz.2]; simp
      · rw [not_and_or] at hz
        have := quad_pos hp hdet (u := n01) (v := n11) hz
        exact this.le
    linarith
  · have h1 := quad_pos hp hdet (Or.inr h : n00 ≠ 0 ∨ n01 ≠ 0)
    have h2 := quad_pos hp hdet (Or.inl h : n01 ≠ 0 ∨ n11 ≠ 0)
    linarith
  · have h2 := quad_pos hp hdet (Or.inr h : n01 ≠ 0 ∨ n11 ≠ 0)
    have h1 : 0 ≤ p * n00 ^ 2 + 2 * q * n00 * n01 + r * n01 ^ 2 := by
      by_cases hz : n00 = 0 ∧ n01 = 0
      · rw [hz.1, hz.2]; simp
      · rw [not_and_or] at hz
        have := quad_pos hp hdet (u := n00) (v := n01) hz
        exact this.le
    linarith

/-- Real data of the momentum columns `B, D` of a symplectic path, the Hessian
entries that drive `B`, and a continuous argument `ψ` of `det (B - i D)`. -/
private structure VD where
  b00 : ℝ → ℝ
  b01 : ℝ → ℝ
  b10 : ℝ → ℝ
  b11 : ℝ → ℝ
  d00 : ℝ → ℝ
  d01 : ℝ → ℝ
  d10 : ℝ → ℝ
  d11 : ℝ → ℝ
  s02 : ℝ → ℝ
  s12 : ℝ → ℝ
  s22 : ℝ → ℝ
  s23 : ℝ → ℝ
  s03 : ℝ → ℝ
  s13 : ℝ → ℝ
  s33 : ℝ → ℝ
  ψ : ℝ → ℝ

namespace VD

variable (V : VD)

def detB (t : ℝ) : ℝ := V.b00 t * V.b11 t - V.b01 t * V.b10 t
def detD (t : ℝ) : ℝ := V.d00 t * V.d11 t - V.d01 t * V.d10 t
def n00 (t : ℝ) : ℝ := V.d00 t * V.b11 t - V.d01 t * V.b10 t
def n01 (t : ℝ) : ℝ := -V.d00 t * V.b01 t + V.d01 t * V.b00 t
def n10 (t : ℝ) : ℝ := V.d10 t * V.b11 t - V.d11 t * V.b10 t
def n11 (t : ℝ) : ℝ := -V.d10 t * V.b01 t + V.d11 t * V.b00 t
def trN (t : ℝ) : ℝ := V.n00 t + V.n11 t
def g (t : ℝ) : ℂ :=
  ((V.detB t - V.detD t : ℝ) : ℂ) + ((-V.trN t : ℝ) : ℂ) * Complex.I
noncomputable def μ (t : ℝ) : ℝ := V.ψ t - Complex.arg (V.g t / (V.detB t : ℂ))
def bd00 (t : ℝ) : ℝ :=
  V.b00 t * V.s02 t + V.b10 t * V.s12 t + V.d00 t * V.s22 t + V.d10 t * V.s23 t
def bd01 (t : ℝ) : ℝ :=
  V.b01 t * V.s02 t + V.b11 t * V.s12 t + V.d01 t * V.s22 t + V.d11 t * V.s23 t
def bd10 (t : ℝ) : ℝ :=
  V.b00 t * V.s03 t + V.b10 t * V.s13 t + V.d00 t * V.s23 t + V.d10 t * V.s33 t
def bd11 (t : ℝ) : ℝ :=
  V.b01 t * V.s03 t + V.b11 t * V.s13 t + V.d01 t * V.s23 t + V.d11 t * V.s33 t

structure Good : Prop where
  hb00 : ∀ t, HasDerivAt V.b00 (V.bd00 t) t
  hb01 : ∀ t, HasDerivAt V.b01 (V.bd01 t) t
  hb10 : ∀ t, HasDerivAt V.b10 (V.bd10 t) t
  hb11 : ∀ t, HasDerivAt V.b11 (V.bd11 t) t
  hd00 : ∀ t, DifferentiableAt ℝ V.d00 t
  hd01 : ∀ t, DifferentiableAt ℝ V.d01 t
  hd10 : ∀ t, DifferentiableAt ℝ V.d10 t
  hd11 : ∀ t, DifferentiableAt ℝ V.d11 t
  lag : ∀ t, V.b00 t * V.d01 t + V.b10 t * V.d11 t = V.b01 t * V.d00 t + V.b11 t * V.d10 t
  rank : ∀ t k0 k1 : ℝ, V.b00 t * k0 + V.b01 t * k1 = 0 → V.b10 t * k0 + V.b11 t * k1 = 0 →
    V.d00 t * k0 + V.d01 t * k1 = 0 → V.d10 t * k0 + V.d11 t * k1 = 0 → k0 = 0 ∧ k1 = 0
  s22_pos : ∀ t, 0 < V.s22 t
  sdet_pos : ∀ t, 0 < V.s22 t * V.s33 t - V.s23 t ^ 2
  ψ_cont : Continuous V.ψ
  polar_re : ∀ t, (V.g t).re = ‖V.g t‖ * Real.cos (V.ψ t)
  polar_im : ∀ t, (V.g t).im = ‖V.g t‖ * Real.sin (V.ψ t)

variable {V}

lemma g_re (t : ℝ) : (V.g t).re = V.detB t - V.detD t := by simp [VD.g]
lemma g_im (t : ℝ) : (V.g t).im = -V.trN t := by simp [VD.g]

lemma n_symm (hV : V.Good) (t : ℝ) : V.n01 t = V.n10 t := by
  unfold VD.n01 VD.n10; linear_combination hV.lag t

lemma det_n (t : ℝ) : V.n00 t * V.n11 t - V.n01 t * V.n10 t = V.detD t * V.detB t := by
  unfold VD.n00 VD.n01 VD.n10 VD.n11 VD.detD VD.detB; ring

lemma cont_b00 (hV : V.Good) : Continuous V.b00 :=
  continuous_iff_continuousAt.2 fun t => (hV.hb00 t).continuousAt
lemma cont_b01 (hV : V.Good) : Continuous V.b01 :=
  continuous_iff_continuousAt.2 fun t => (hV.hb01 t).continuousAt
lemma cont_b10 (hV : V.Good) : Continuous V.b10 :=
  continuous_iff_continuousAt.2 fun t => (hV.hb10 t).continuousAt
lemma cont_b11 (hV : V.Good) : Continuous V.b11 :=
  continuous_iff_continuousAt.2 fun t => (hV.hb11 t).continuousAt
lemma cont_d00 (hV : V.Good) : Continuous V.d00 :=
  continuous_iff_continuousAt.2 fun t => (hV.hd00 t).continuousAt
lemma cont_d01 (hV : V.Good) : Continuous V.d01 :=
  continuous_iff_continuousAt.2 fun t => (hV.hd01 t).continuousAt
lemma cont_d10 (hV : V.Good) : Continuous V.d10 :=
  continuous_iff_continuousAt.2 fun t => (hV.hd10 t).continuousAt
lemma cont_d11 (hV : V.Good) : Continuous V.d11 :=
  continuous_iff_continuousAt.2 fun t => (hV.hd11 t).continuousAt

lemma cont_detB (hV : V.Good) : Continuous V.detB := by
  unfold VD.detB
  exact ((cont_b00 hV).mul (cont_b11 hV)).sub ((cont_b01 hV).mul (cont_b10 hV))

lemma cont_g (hV : V.Good) : Continuous V.g := by
  have hdD : Continuous V.detD := by
    unfold VD.detD
    exact ((cont_d00 hV).mul (cont_d11 hV)).sub ((cont_d01 hV).mul (cont_d10 hV))
  have htr : Continuous V.trN := by
    unfold VD.trN VD.n00 VD.n11
    exact (((cont_d00 hV).mul (cont_b11 hV)).sub ((cont_d01 hV).mul (cont_b10 hV))).add
      ((((cont_d10 hV).neg).mul (cont_b01 hV)).add ((cont_d11 hV).mul (cont_b00 hV)))
  unfold VD.g
  exact (Complex.continuous_ofReal.comp ((cont_detB hV).sub hdD)).add
    ((Complex.continuous_ofReal.comp htr.neg).mul continuous_const)

/-- Away from crossings, `g / det B` lies in the slit plane: its argument is the
bounded part of the vertical angle. -/
lemma w_slit (hV : V.Good) {t : ℝ} (hB : V.detB t ≠ 0) :
    V.g t / (V.detB t : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, Complex.div_ofReal_re, Complex.div_ofReal_im,
    g_re, g_im]
  by_cases htr : V.trN t = 0
  · left
    have hs := n_symm hV t
    have hdet := det_n (V := V) t
    have h11 : V.n11 t = -V.n00 t := by unfold VD.trN at htr; linarith
    have hDB : V.detD t * V.detB t ≤ 0 := by
      rw [← hdet, h11, ← hs]; nlinarith [sq_nonneg (V.n00 t), sq_nonneg (V.n01 t)]
    have hsq : 0 < V.detB t ^ 2 := by positivity
    have hprod : 0 < (V.detB t - V.detD t) * V.detB t := by nlinarith
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hprod with h | h
    · exact div_pos h.1 h.2
    · exact div_pos_of_neg_of_neg h.1 h.2
  · right
    exact div_ne_zero (neg_ne_zero.mpr htr) hB

end VD

private lemma cos_even_mul_pi {m : ℤ} (h : Even m) : Real.cos (m * Real.pi) = 1 := by
  obtain ⟨k, hk⟩ := h
  rw [hk]; push_cast
  rw [show ((k : ℝ) + k) * Real.pi = (k : ℤ) * (2 * Real.pi) by ring]
  exact Real.cos_int_mul_two_pi k

private lemma cos_odd_mul_pi {m : ℤ} (h : Odd m) : Real.cos (m * Real.pi) = -1 := by
  obtain ⟨k, hk⟩ := h
  rw [hk]; push_cast
  rw [show (2 * (k : ℝ) + 1) * Real.pi = (k : ℤ) * (2 * Real.pi) + Real.pi by ring]
  exact Real.cos_int_mul_two_pi_add_pi k

namespace VD

variable {V : VD}

/-- Away from crossings, `μ` is an integer multiple of `π` whose parity records the
sign of `det B`, and it lies within `π` of `ψ`. -/
lemma mu_facts (hV : V.Good) {t : ℝ} (hB : V.detB t ≠ 0) :
    (∃ m : ℤ, V.μ t = m * Real.pi ∧ (0 < V.detB t ↔ Even m)) ∧
      |V.ψ t - V.μ t| < Real.pi := by
  set w : ℂ := V.g t / (V.detB t : ℂ) with hw
  have hws : w ∈ Complex.slitPlane := w_slit hV hB
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hws
  have hg0 : V.g t ≠ 0 := by
    intro h; apply hw0; rw [hw, h, zero_div]
  have hG : 0 < ‖V.g t‖ := norm_pos_iff.mpr hg0
  have hμ : V.μ t = V.ψ t - Complex.arg w := rfl
  refine ⟨?_, ?_⟩
  · have hcosψ : Real.cos (V.ψ t) = (V.g t).re / ‖V.g t‖ := by
      rw [hV.polar_re t]; field_simp
    have hsinψ : Real.sin (V.ψ t) = (V.g t).im / ‖V.g t‖ := by
      rw [hV.polar_im t]; field_simp
    have hwre : w.re = (V.g t).re / V.detB t := by rw [hw, Complex.div_ofReal_re]
    have hwim : w.im = (V.g t).im / V.detB t := by rw [hw, Complex.div_ofReal_im]
    have hwn : ‖w‖ = ‖V.g t‖ / |V.detB t| := by
      rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hcosθ : Real.cos (Complex.arg w) = w.re / ‖w‖ := Complex.cos_arg hw0
    have hsinθ : Real.sin (Complex.arg w) = w.im / ‖w‖ := Complex.sin_arg w
    have hGsq : ‖V.g t‖ ^ 2 = (V.g t).re ^ 2 + (V.g t).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have habs : 0 < |V.detB t| := abs_pos.mpr hB
    have hsinμ : Real.sin (V.μ t) = 0 := by
      rw [hμ, Real.sin_sub, hcosθ, hsinθ, hcosψ, hsinψ, hwre, hwim, hwn]
      field_simp
      ring
    have hcosμ : Real.cos (V.μ t) * V.detB t = |V.detB t| := by
      rw [hμ, Real.cos_sub, hcosθ, hsinθ, hcosψ, hsinψ, hwre, hwim, hwn]
      field_simp
      linear_combination -hGsq
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsinμ
    refine ⟨m, hm.symm, ?_⟩
    rw [← hm] at hcosμ
    constructor
    · intro hpos
      rcases Int.even_or_odd m with he | ho
      · exact he
      · rw [cos_odd_mul_pi ho, abs_of_pos hpos] at hcosμ; linarith
    · intro he
      rw [cos_even_mul_pi he, one_mul] at hcosμ
      rcases lt_or_gt_of_ne hB with hneg | hpos
      · rw [abs_of_neg hneg] at hcosμ; linarith
      · exact hpos
  · rw [show V.ψ t - V.μ t = Complex.arg w by rw [hμ]; ring, abs_lt]
    refine ⟨Complex.neg_pi_lt_arg w, ?_⟩
    rw [Complex.arg_lt_pi_iff]
    rcases Complex.mem_slitPlane_iff.mp hws with h | h
    · exact Or.inl h.le
    · exact Or.inr h

end VD

/-- A multiple of `π` within `π` of a point of `(kπ, (k+1)π)` is `kπ` or `(k+1)π`. -/
private lemma int_near {m k : ℤ} {x μ : ℝ} (hμ : μ = m * Real.pi) (hx : |x - μ| < Real.pi)
    (hk1 : (k : ℝ) * Real.pi < x) (hk2 : x < (k + 1) * Real.pi) : m = k ∨ m = k + 1 := by
  have hπ := Real.pi_pos
  rw [abs_lt] at hx
  have h1 : ((k : ℝ) - 1) < m := by
    have : ((k : ℝ) - 1) * Real.pi < m * Real.pi := by nlinarith
    exact lt_of_mul_lt_mul_right this hπ.le
  have h2 : (m : ℝ) < k + 2 := by
    have : (m : ℝ) * Real.pi < (k + 2) * Real.pi := by nlinarith
    exact lt_of_mul_lt_mul_right this hπ.le
  have h1i : k - 1 < m := by exact_mod_cast h1
  have h2i : m < k + 2 := by exact_mod_cast h2
  omega

/-- On `(kπ, (k+1)π)` the sine is positive exactly when `k` is even. -/
private lemma sin_pos_iff_even {k : ℤ} {x : ℝ} (hk1 : (k : ℝ) * Real.pi < x)
    (hk2 : x < (k + 1) * Real.pi) : 0 < Real.sin x ↔ Even k := by
  have hy : 0 < x - k * Real.pi := by linarith
  have hy2 : x - k * Real.pi < Real.pi := by linarith
  have hs : 0 < Real.sin (x - k * Real.pi) := Real.sin_pos_of_pos_of_lt_pi hy hy2
  have hx : Real.sin x = (-1) ^ k * Real.sin (x - k * Real.pi) := by
    have := Real.sin_add_int_mul_pi (x - k * Real.pi) k
    rw [sub_add_cancel] at this; exact this
  rcases Int.even_or_odd k with he | ho
  · rw [hx, he.neg_one_zpow, one_mul]; exact ⟨fun _ => he, fun _ => hs⟩
  · rw [hx, ho.neg_one_zpow]
    constructor
    · intro h; nlinarith
    · intro he; exact absurd he (Int.not_even_iff_odd.mpr ho)

namespace VD

variable {V : VD}

/-- Away from crossings, `det B` stays nonzero and `μ` is locally constant. -/
lemma const_near (hV : V.Good) {t₀ : ℝ} (hB : V.detB t₀ ≠ 0) :
    ∃ ε > 0, ∀ s, |s - t₀| < ε → V.detB s ≠ 0 ∧ V.μ s = V.μ t₀ := by
  have hcB := (cont_detB hV).continuousAt (x := t₀)
  have hne : ∀ᶠ s in nhds t₀, V.detB s ≠ 0 := hcB.eventually_ne hB
  have hwc : ContinuousAt (fun s => V.g s / (V.detB s : ℂ)) t₀ :=
    ((cont_g hV).continuousAt).div (Complex.continuous_ofReal.continuousAt.comp hcB)
      (by exact_mod_cast hB)
  have hac : ContinuousAt (fun s => Complex.arg (V.g s / (V.detB s : ℂ))) t₀ :=
    ContinuousAt.comp (f := fun s => V.g s / (V.detB s : ℂ))
      (Complex.continuousAt_arg (w_slit hV hB)) hwc
  have hμc : ContinuousAt V.μ t₀ := hV.ψ_cont.continuousAt.sub hac
  have hclose : ∀ᶠ s in nhds t₀, V.μ s ∈ Metric.ball (V.μ t₀) Real.pi :=
    hμc (Metric.ball_mem_nhds _ Real.pi_pos)
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp (hne.and hclose)
  refine ⟨ε, hε, fun s hs => ?_⟩
  obtain ⟨hBs, hcl⟩ := h (show dist s t₀ < ε by rwa [Real.dist_eq])
  refine ⟨hBs, ?_⟩
  obtain ⟨⟨m, hm, -⟩, -⟩ := mu_facts hV hBs
  obtain ⟨⟨m₀, hm₀, -⟩, -⟩ := mu_facts hV hB
  rw [Metric.mem_ball, Real.dist_eq, hm, hm₀, ← sub_mul, abs_mul,
    abs_of_pos Real.pi_pos] at hcl
  have h1 : |((m - m₀ : ℤ) : ℝ)| < 1 := by
    push_cast
    exact (mul_lt_iff_lt_one_left Real.pi_pos).mp hcl
  have h2 : |m - m₀| < 1 := by exact_mod_cast h1
  have h3 : m = m₀ := by rw [Int.abs_lt_one_iff] at h2; omega
  rw [hm, hm₀, h3]

/-- At a simple crossing (`det B = 0`, `B ≠ 0`) the crossing is isolated and `μ`
jumps up by `π`. -/
lemma jump_simple (hV : V.Good) {t₀ : ℝ} (h0 : V.detB t₀ = 0)
    (hBne : ¬ (V.b00 t₀ = 0 ∧ V.b01 t₀ = 0 ∧ V.b10 t₀ = 0 ∧ V.b11 t₀ = 0)) :
    ∃ ε > 0, (∀ s, s ≠ t₀ → |s - t₀| < ε → V.detB s ≠ 0) ∧
      (∀ s₁ s₂, t₀ - ε < s₁ → s₁ < t₀ → t₀ < s₂ → s₂ < t₀ + ε → V.μ s₁ ≤ V.μ s₂) := by
  have hsym := n_symm hV t₀
  have hdetn := det_n (V := V) t₀
  rw [h0, mul_zero] at hdetn
  have hB0 : V.b00 t₀ * V.b11 t₀ - V.b01 t₀ * V.b10 t₀ = 0 := h0
  -- `N = D adj B` is nonzero
  have hN : V.n00 t₀ ≠ 0 ∨ V.n01 t₀ ≠ 0 ∨ V.n11 t₀ ≠ 0 := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨h00, h01, h11⟩ := hcon
    have h10 : V.n10 t₀ = 0 := by rw [← hsym, h01]
    unfold VD.n00 at h00; unfold VD.n01 at h01; unfold VD.n10 at h10; unfold VD.n11 at h11
    apply hBne
    have hA := hV.rank t₀ (V.b11 t₀) (-V.b10 t₀) (by linear_combination hB0) (by ring)
      (by linear_combination h00) (by linear_combination h10)
    have hC := hV.rank t₀ (-V.b01 t₀) (V.b00 t₀) (by ring) (by linear_combination hB0)
      (by linear_combination h01) (by linear_combination h11)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hA.1, hA.2, hC.1, hC.2]
  have hrank : V.n00 t₀ * V.n11 t₀ = V.n01 t₀ ^ 2 := by
    linear_combination hdetn - V.n01 t₀ * hsym
  set T := V.s22 t₀ * V.n00 t₀ + 2 * V.s23 t₀ * V.n01 t₀ + V.s33 t₀ * V.n11 t₀ with hT
  have hkey : 0 < V.trN t₀ * T := by
    unfold VD.trN
    exact trace_mul_pos (hV.s22_pos t₀) (hV.sdet_pos t₀) hrank hN
  have hdB : HasDerivAt V.detB T t₀ := by
    have h := ((hV.hb00 t₀).mul (hV.hb11 t₀)).sub ((hV.hb01 t₀).mul (hV.hb10 t₀))
    have hfun : V.detB = V.b00 * V.b11 - V.b01 * V.b10 := by
      funext y; simp [VD.detB]
    rw [hfun]
    refine h.congr_deriv ?_
    have hsymU : -V.d00 t₀ * V.b01 t₀ + V.d01 t₀ * V.b00 t₀ =
        V.d10 t₀ * V.b11 t₀ - V.d11 t₀ * V.b10 t₀ := hsym
    rw [hT]
    unfold VD.bd00 VD.bd01 VD.bd10 VD.bd11 VD.n00 VD.n01 VD.n11
    linear_combination -(V.s23 t₀ * hsymU - (V.s02 t₀ + V.s13 t₀) * hB0)
  have htr0 : V.trN t₀ ≠ 0 := by
    intro h; rw [h, zero_mul] at hkey; exact lt_irrefl 0 hkey
  have hT0 : T ≠ 0 := by
    intro h; rw [h, mul_zero] at hkey; exact lt_irrefl 0 hkey
  have hg0 : V.g t₀ ≠ 0 := by
    intro h; apply htr0; have := g_im (V := V) t₀; rw [h, Complex.zero_im] at this; linarith
  have hG : 0 < ‖V.g t₀‖ := norm_pos_iff.mpr hg0
  have hsinψ : Real.sin (V.ψ t₀) = -V.trN t₀ / ‖V.g t₀‖ := by
    rw [← g_im, hV.polar_im t₀]; field_simp
  have hsin0 : Real.sin (V.ψ t₀) ≠ 0 := by
    rw [hsinψ]; exact div_ne_zero (neg_ne_zero.mpr htr0) hG.ne'
  set k : ℤ := ⌊V.ψ t₀ / Real.pi⌋ with hk
  have hk1 : (k : ℝ) * Real.pi < V.ψ t₀ := by
    have hle : (k : ℝ) ≤ V.ψ t₀ / Real.pi := Int.floor_le _
    have hle2 : (k : ℝ) * Real.pi ≤ V.ψ t₀ := by
      rwa [le_div_iff₀ Real.pi_pos] at hle
    rcases hle2.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; apply hsin0; rw [← heq]; exact Real.sin_int_mul_pi k
  have hk2 : V.ψ t₀ < (k + 1) * Real.pi := by
    have hlt : V.ψ t₀ / Real.pi < (k : ℝ) + 1 := Int.lt_floor_add_one _
    rwa [div_lt_iff₀ Real.pi_pos] at hlt
  obtain ⟨ε₁, hε₁, hψ⟩ := Metric.eventually_nhds_iff.mp
    (hV.ψ_cont.continuousAt (x := t₀) (Ioo_mem_nhds hk1 hk2))
  have hmem : ∀ s, |s - t₀| < ε₁ → V.detB s ≠ 0 → ∃ m : ℤ, V.μ s = m * Real.pi ∧
      (0 < V.detB s ↔ Even m) ∧ (m = k ∨ m = k + 1) := by
    intro s hs hBs
    obtain ⟨⟨m, hm, hpar⟩, hcl⟩ := mu_facts hV hBs
    have hψs := hψ (show dist s t₀ < ε₁ by rwa [Real.dist_eq])
    exact ⟨m, hm, hpar, int_near hm hcl hψs.1 hψs.2⟩
  rcases lt_or_gt_of_ne hT0 with hTneg | hTpos
  · -- `det B` decreases through the crossing; `sin ψ > 0` and `k` is even
    obtain ⟨ε₂, hε₂, hsg⟩ := sign_near_of_hasDerivAt_neg hdB h0 hTneg
    have htrneg : V.trN t₀ < 0 := by
      by_contra hc
      have hc2 : 0 ≤ V.trN t₀ := le_of_not_gt hc
      have := mul_nonpos_of_nonneg_of_nonpos hc2 hTneg.le; linarith
    have hkeven : Even k := by
      rw [← sin_pos_iff_even hk1 hk2, hsinψ]
      exact div_pos (by linarith) hG
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩
    · intro s hs hsd
      rw [abs_lt] at hsd
      rcases lt_or_gt_of_ne hs with hlt | hgt
      · exact ((hsg s).2 (by linarith [min_le_right ε₁ ε₂]) hlt).ne'
      · exact ((hsg s).1 hgt (by linarith [min_le_right ε₁ ε₂])).ne
    · intro s₁ s₂ h1 h2 h3 h4
      have hB1 : 0 < V.detB s₁ := (hsg s₁).2 (by linarith [min_le_right ε₁ ε₂]) h2
      have hB2 : V.detB s₂ < 0 := (hsg s₂).1 h3 (by linarith [min_le_right ε₁ ε₂])
      have hs1 : |s₁ - t₀| < ε₁ := by
        rw [abs_lt]; constructor <;> linarith [min_le_left ε₁ ε₂]
      obtain ⟨m₁, hm₁, hp₁, hc₁⟩ := hmem s₁ hs1 hB1.ne'
      have hs2 : |s₂ - t₀| < ε₁ := by
        rw [abs_lt]; constructor <;> linarith [min_le_left ε₁ ε₂]
      obtain ⟨m₂, hm₂, hp₂, hc₂⟩ := hmem s₂ hs2 hB2.ne
      have he₁ : Even m₁ := hp₁.mp hB1
      have hne₂ : ¬ Even m₂ := fun h => absurd (hp₂.mpr h) (by linarith)
      have hm₁k : m₁ = k := by
        rcases hc₁ with h | h
        · exact h
        · exfalso; rw [h, Int.even_add_one] at he₁; exact he₁ hkeven
      have hm₂k : m₂ = k + 1 := by
        rcases hc₂ with h | h
        · exfalso; rw [h] at hne₂; exact hne₂ hkeven
        · exact h
      rw [hm₁, hm₂, hm₁k, hm₂k]; push_cast
      nlinarith [Real.pi_pos]
  · -- `det B` increases through the crossing; `sin ψ < 0` and `k` is odd
    obtain ⟨ε₂, hε₂, hsg⟩ := sign_near_of_hasDerivAt hdB h0 hTpos
    have htrpos : 0 < V.trN t₀ := by
      by_contra hc
      have hc2 : V.trN t₀ ≤ 0 := le_of_not_gt hc
      have := mul_nonpos_of_nonpos_of_nonneg hc2 hTpos.le; linarith
    have hkodd : ¬ Even k := by
      rw [← sin_pos_iff_even hk1 hk2, hsinψ]
      exact not_lt.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hG.le)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩
    · intro s hs hsd
      rw [abs_lt] at hsd
      rcases lt_or_gt_of_ne hs with hlt | hgt
      · exact ((hsg s).2 (by linarith [min_le_right ε₁ ε₂]) hlt).ne
      · exact ((hsg s).1 hgt (by linarith [min_le_right ε₁ ε₂])).ne'
    · intro s₁ s₂ h1 h2 h3 h4
      have hB1 : V.detB s₁ < 0 := (hsg s₁).2 (by linarith [min_le_right ε₁ ε₂]) h2
      have hB2 : 0 < V.detB s₂ := (hsg s₂).1 h3 (by linarith [min_le_right ε₁ ε₂])
      have hs1 : |s₁ - t₀| < ε₁ := by
        rw [abs_lt]; constructor <;> linarith [min_le_left ε₁ ε₂]
      obtain ⟨m₁, hm₁, hp₁, hc₁⟩ := hmem s₁ hs1 hB1.ne
      have hs2 : |s₂ - t₀| < ε₁ := by
        rw [abs_lt]; constructor <;> linarith [min_le_left ε₁ ε₂]
      obtain ⟨m₂, hm₂, hp₂, hc₂⟩ := hmem s₂ hs2 hB2.ne'
      have hne₁ : ¬ Even m₁ := fun h => absurd (hp₁.mpr h) (by linarith)
      have he₂ : Even m₂ := hp₂.mp hB2
      have hm₁k : m₁ = k := by
        rcases hc₁ with h | h
        · exact h
        · exfalso; rw [h, Int.even_add_one] at hne₁; exact hne₁ hkodd
      have hm₂k : m₂ = k + 1 := by
        rcases hc₂ with h | h
        · exfalso; rw [h] at he₂; exact hkodd he₂
        · exact h
      rw [hm₁, hm₂, hm₁k, hm₂k]; push_cast
      nlinarith [Real.pi_pos]

end VD

/-- On `(-π, π)`, the sign of `sin x` is the sign of `x`. -/
private lemma pos_of_sin_pos {x : ℝ} (hx : |x| < Real.pi) (hs : 0 < Real.sin x) : 0 < x := by
  rw [abs_lt] at hx
  by_contra hc
  have hc2 : x ≤ 0 := le_of_not_gt hc
  have : 0 ≤ Real.sin (-x) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [Real.sin_neg] at this; linarith

private lemma neg_of_sin_neg {x : ℝ} (hx : |x| < Real.pi) (hs : Real.sin x < 0) : x < 0 := by
  rw [abs_lt] at hx
  by_contra hc
  have hc2 : 0 ≤ x := le_of_not_gt hc
  have : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hc2 (by linarith)
  linarith

namespace VD

variable {V : VD}

/-- At a double crossing (`B = 0`) the crossing is isolated, `ψ` passes a multiple of
`π` increasingly, and `μ` does not decrease. -/
lemma jump_double (hV : V.Good) {t₀ : ℝ} (hb00 : V.b00 t₀ = 0) (hb01 : V.b01 t₀ = 0)
    (hb10 : V.b10 t₀ = 0) (hb11 : V.b11 t₀ = 0) :
    ∃ ε > 0, (∀ s, s ≠ t₀ → |s - t₀| < ε → V.detB s ≠ 0) ∧
      (∀ s₁ s₂, t₀ - ε < s₁ → s₁ < t₀ → t₀ < s₂ → s₂ < t₀ + ε → V.μ s₁ ≤ V.μ s₂) := by
  -- `det D ≠ 0`
  have hD : V.detD t₀ ≠ 0 := by
    intro hD0
    have hD0u : V.d00 t₀ * V.d11 t₀ - V.d01 t₀ * V.d10 t₀ = 0 := hD0
    have hA := hV.rank t₀ (V.d11 t₀) (-V.d10 t₀) (by rw [hb00, hb01]; ring)
      (by rw [hb10, hb11]; ring) (by linear_combination hD0u) (by ring)
    have hC := hV.rank t₀ (-V.d01 t₀) (V.d00 t₀) (by rw [hb00, hb01]; ring)
      (by rw [hb10, hb11]; ring) (by ring) (by linear_combination hD0u)
    have hd00 : V.d00 t₀ = 0 := hC.2
    have hd10 : V.d10 t₀ = 0 := by linarith [hA.2]
    have hE := hV.rank t₀ 1 0 (by rw [hb00, hb01]; ring) (by rw [hb10, hb11]; ring)
      (by rw [hd00]; ring) (by rw [hd10]; ring)
    exact one_ne_zero hE.1
  have htr0 : V.trN t₀ = 0 := by
    unfold VD.trN VD.n00 VD.n11; rw [hb00, hb01, hb10, hb11]; ring
  have hdB0 : V.detB t₀ = 0 := by
    unfold VD.detB; rw [hb00, hb01, hb10, hb11]; ring
  have hgre : (V.g t₀).re = -V.detD t₀ := by rw [g_re, hdB0]; ring
  have hgim : (V.g t₀).im = 0 := by rw [g_im, htr0]; ring
  have hg0 : V.g t₀ ≠ 0 := by
    intro h; apply hD; have := hgre; rw [h, Complex.zero_re] at this; linarith
  have hG0 : 0 < ‖V.g t₀‖ := norm_pos_iff.mpr hg0
  have hsinψ0 : Real.sin (V.ψ t₀) = 0 := by
    have := hV.polar_im t₀
    rw [hgim] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hG0.ne'
  have hcosψ0 : Real.cos (V.ψ t₀) = -V.detD t₀ / ‖V.g t₀‖ := by
    rw [← hgre, hV.polar_re t₀]; field_simp
  obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp hsinψ0
  -- derivative of `tr N` at the crossing
  have htrN : HasDerivAt V.trN ((V.s22 t₀ + V.s33 t₀) * V.detD t₀) t₀ := by
    have h := ((((hV.hd00 t₀).hasDerivAt.mul (hV.hb11 t₀)).sub
      ((hV.hd01 t₀).hasDerivAt.mul (hV.hb10 t₀))).add
      ((((hV.hd10 t₀).hasDerivAt.neg).mul (hV.hb01 t₀)).add
        ((hV.hd11 t₀).hasDerivAt.mul (hV.hb00 t₀))))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    · unfold VD.bd00 VD.bd01 VD.bd10 VD.bd11 VD.detD
      rw [hb00, hb01, hb10, hb11]; simp only [Pi.neg_apply]; ring
    · simp only [VD.trN, VD.n00, VD.n11, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Pi.neg_apply]
  -- the crossing is isolated: `det B (s) / (s - t₀)^2 → det Ḃ(t₀) ≠ 0`
  have hslope : ∀ {f : ℝ → ℝ} {f' : ℝ}, HasDerivAt f f' t₀ → f t₀ = 0 →
      Filter.Tendsto (fun s => f s / (s - t₀)) (nhdsWithin t₀ {t₀}ᶜ) (nhds f') := by
    intro f f' hf h0
    refine (hasDerivAt_iff_tendsto_slope.mp hf).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field, h0, sub_zero]
  have hlim := ((hslope (hV.hb00 t₀) hb00).mul (hslope (hV.hb11 t₀) hb11)).sub
    ((hslope (hV.hb01 t₀) hb01).mul (hslope (hV.hb10 t₀) hb10))
  have hΔ : V.bd00 t₀ * V.bd11 t₀ - V.bd01 t₀ * V.bd10 t₀ =
      (V.s22 t₀ * V.s33 t₀ - V.s23 t₀ ^ 2) * V.detD t₀ := by
    unfold VD.bd00 VD.bd01 VD.bd10 VD.bd11 VD.detD; rw [hb00, hb01, hb10, hb11]; ring
  have hΔne : V.bd00 t₀ * V.bd11 t₀ - V.bd01 t₀ * V.bd10 t₀ ≠ 0 := by
    rw [hΔ]; exact mul_ne_zero (hV.sdet_pos t₀).ne' hD
  obtain ⟨ε₃, hε₃, h3⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (hlim.eventually_ne hΔne))
  have hiso : ∀ s, s ≠ t₀ → |s - t₀| < ε₃ → V.detB s ≠ 0 := by
    intro s hs hsd
    have hq := h3 (show dist s t₀ < ε₃ by rwa [Real.dist_eq])
      (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hs)
    intro hB
    apply hq
    have hne : s - t₀ ≠ 0 := sub_ne_zero.mpr hs
    have hBu : V.b00 s * V.b11 s - V.b01 s * V.b10 s = 0 := hB
    field_simp
    linear_combination hBu
  -- the sign of `ψ s - ψ t₀` is the sign of `s - t₀`
  have hs33 : 0 < V.s33 t₀ := by
    have h1 := hV.s22_pos t₀; have h2 := hV.sdet_pos t₀
    by_contra hc
    have hc2 : V.s33 t₀ ≤ 0 := le_of_not_gt hc
    nlinarith [sq_nonneg (V.s23 t₀)]
  have hf : HasDerivAt (fun s => V.detD t₀ * V.trN s)
      (V.detD t₀ * ((V.s22 t₀ + V.s33 t₀) * V.detD t₀)) t₀ := htrN.const_mul _
  have hfpos : 0 < V.detD t₀ * ((V.s22 t₀ + V.s33 t₀) * V.detD t₀) := by
    have hsq : 0 < V.detD t₀ ^ 2 := by positivity
    have hsum : 0 < V.s22 t₀ + V.s33 t₀ := by linarith [hV.s22_pos t₀]
    nlinarith
  obtain ⟨ε₄, hε₄, hsg⟩ := sign_near_of_hasDerivAt hf (by simp [htr0]) hfpos
  obtain ⟨ε₅, hε₅, hψc⟩ := Metric.eventually_nhds_iff.mp
    (hV.ψ_cont.continuousAt (x := t₀) (Metric.ball_mem_nhds _ Real.pi_pos))
  -- sine of the angle increment
  have hsin_inc : ∀ s, V.detD t₀ * V.trN s ≠ 0 →
      Real.sin (V.ψ s - V.ψ t₀) * (‖V.g s‖ * ‖V.g t₀‖) = V.detD t₀ * V.trN s := by
    intro s hfs
    have hgs : V.g s ≠ 0 := by
      intro h; apply hfs
      have := g_im (V := V) s; rw [h, Complex.zero_im] at this
      rw [show V.trN s = 0 by linarith]; ring
    have hGs : 0 < ‖V.g s‖ := norm_pos_iff.mpr hgs
    have hsins : Real.sin (V.ψ s) = -V.trN s / ‖V.g s‖ := by
      rw [← g_im, hV.polar_im s]; field_simp
    rw [Real.sin_sub, hsinψ0, hcosψ0, hsins]
    field_simp
    ring
  refine ⟨min ε₃ (min ε₄ ε₅), lt_min hε₃ (lt_min hε₄ hε₅), ?_, ?_⟩
  · intro s hs hsd
    exact hiso s hs (lt_of_lt_of_le hsd (min_le_left _ _))
  · intro s₁ s₂ h1 h2 h3 h4
    have hm3 := min_le_left ε₃ (min ε₄ ε₅)
    have hm4 := le_trans (min_le_right ε₃ (min ε₄ ε₅)) (min_le_left ε₄ ε₅)
    have hm5 := le_trans (min_le_right ε₃ (min ε₄ ε₅)) (min_le_right ε₄ ε₅)
    -- left point: `ψ s₁ < j π`
    have hf1 : V.detD t₀ * V.trN s₁ < 0 := (hsg s₁).2 (by linarith) h2
    have hψ1 : |V.ψ s₁ - V.ψ t₀| < Real.pi := by
      have := hψc (show dist s₁ t₀ < ε₅ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rwa [Metric.mem_ball, Real.dist_eq] at this
    have hs1 : Real.sin (V.ψ s₁ - V.ψ t₀) < 0 := by
      have he := hsin_inc s₁ hf1.ne
      have hpos : 0 < ‖V.g s₁‖ * ‖V.g t₀‖ := by
        have hgs : V.g s₁ ≠ 0 := by
          intro h; have := g_im (V := V) s₁; rw [h, Complex.zero_im] at this
          have htr : V.trN s₁ = 0 := by linarith
          rw [htr, mul_zero] at hf1; exact lt_irrefl 0 hf1
        exact mul_pos (norm_pos_iff.mpr hgs) hG0
      by_contra hc
      have hc2 : 0 ≤ Real.sin (V.ψ s₁ - V.ψ t₀) := le_of_not_gt hc
      have := mul_nonneg hc2 hpos.le
      linarith
    have hlt1 : V.ψ s₁ < V.ψ t₀ := by linarith [neg_of_sin_neg hψ1 hs1]
    -- right point: `ψ s₂ > j π`
    have hf2 : 0 < V.detD t₀ * V.trN s₂ := (hsg s₂).1 h3 (by linarith)
    have hψ2 : |V.ψ s₂ - V.ψ t₀| < Real.pi := by
      have := hψc (show dist s₂ t₀ < ε₅ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rwa [Metric.mem_ball, Real.dist_eq] at this
    have hs2 : 0 < Real.sin (V.ψ s₂ - V.ψ t₀) := by
      have he := hsin_inc s₂ hf2.ne'
      have hgs : V.g s₂ ≠ 0 := by
        intro h; have := g_im (V := V) s₂; rw [h, Complex.zero_im] at this
        have htr : V.trN s₂ = 0 := by linarith
        rw [htr, mul_zero] at hf2; exact lt_irrefl 0 hf2
      have hpos : 0 < ‖V.g s₂‖ * ‖V.g t₀‖ := mul_pos (norm_pos_iff.mpr hgs) hG0
      by_contra hc
      have hc2 : Real.sin (V.ψ s₂ - V.ψ t₀) ≤ 0 := le_of_not_gt hc
      have := mul_nonpos_of_nonpos_of_nonneg hc2 hpos.le
      linarith
    have hgt2 : V.ψ t₀ < V.ψ s₂ := by linarith [pos_of_sin_pos hψ2 hs2]
    -- integer bookkeeping
    have hB1 : V.detB s₁ ≠ 0 := hiso s₁ (by linarith) (by
      rw [abs_lt]; constructor <;> linarith)
    have hB2 : V.detB s₂ ≠ 0 := hiso s₂ (by linarith) (by
      rw [abs_lt]; constructor <;> linarith)
    obtain ⟨⟨m₁, hm₁, -⟩, hc₁⟩ := mu_facts hV hB1
    obtain ⟨⟨m₂, hm₂, -⟩, hc₂⟩ := mu_facts hV hB2
    rw [abs_lt] at hc₁ hc₂
    have hπ := Real.pi_pos
    have hA1 : (m₁ : ℝ) * Real.pi < ((j : ℝ) + 1) * Real.pi := by
      rw [← hm₁]; nlinarith
    have hA2 : ((j : ℝ) - 1) * Real.pi < (m₂ : ℝ) * Real.pi := by
      rw [← hm₂]; nlinarith
    have hI1 : m₁ < j + 1 := by
      have := lt_of_mul_lt_mul_right hA1 hπ.le; exact_mod_cast this
    have hI2 : j - 1 < m₂ := by
      have := lt_of_mul_lt_mul_right hA2 hπ.le; exact_mod_cast this
    have hle : m₁ ≤ m₂ := by omega
    rw [hm₁, hm₂]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hπ.le

/-- Every crossing is isolated, and `μ` does not decrease across it. -/
lemma jump (hV : V.Good) {t₀ : ℝ} (h0 : V.detB t₀ = 0) :
    ∃ ε > 0, (∀ s, s ≠ t₀ → |s - t₀| < ε → V.detB s ≠ 0) ∧
      (∀ s₁ s₂, t₀ - ε < s₁ → s₁ < t₀ → t₀ < s₂ → s₂ < t₀ + ε → V.μ s₁ ≤ V.μ s₂) := by
  by_cases hB : V.b00 t₀ = 0 ∧ V.b01 t₀ = 0 ∧ V.b10 t₀ = 0 ∧ V.b11 t₀ = 0
  · exact jump_double hV hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
  · exact jump_simple hV h0 hB

end VD

namespace VD

variable {V : VD}

/-- Starting from a non-crossing time, `μ` never drops below its initial value. -/
lemma mu_mono (hV : V.Good) {a b : ℝ} (hB : V.detB a ≠ 0) :
    ∀ s ∈ Set.Icc a b, V.detB s ≠ 0 → V.μ a ≤ V.μ s := by
  by_contra hcon
  simp only [not_forall, not_le] at hcon
  obtain ⟨s0, hs0, hBs0, hμs0⟩ := hcon
  set Fail : Set ℝ := {s | s ∈ Set.Icc a b ∧ V.detB s ≠ 0 ∧ V.μ s < V.μ a} with hFail
  have hmem0 : s0 ∈ Fail := ⟨hs0, hBs0, hμs0⟩
  have hne : Fail.Nonempty := ⟨s0, hmem0⟩
  have hbdd : BddBelow Fail := ⟨a, fun s hs => hs.1.1⟩
  set T := sInf Fail with hT
  have haT : a ≤ T := le_csInf hne (fun s hs => hs.1.1)
  have hTb : T ≤ b := (csInf_le hbdd hmem0).trans hs0.2
  have hbefore : ∀ s ∈ Set.Icc a b, s < T → V.detB s ≠ 0 → V.μ a ≤ V.μ s := by
    intro s hs hsT hBs
    by_contra hc
    have hc2 : V.μ s < V.μ a := lt_of_not_ge hc
    have : T ≤ s := csInf_le hbdd ⟨hs, hBs, hc2⟩
    linarith
  have hafter : ∀ ε > 0, ∃ s ∈ Fail, s < T + ε := by
    intro ε hε
    exact exists_lt_of_csInf_lt hne (show T < T + ε by linarith)
  by_cases hBT : V.detB T = 0
  · have hTa : a < T := lt_of_le_of_ne haT (fun h => hB (by rw [h]; exact hBT))
    obtain ⟨ε, hε, hiso, hjump⟩ := jump hV hBT
    obtain ⟨s₂, hs₂, hs₂T⟩ := hafter ε hε
    have hTs₂ : T ≤ s₂ := csInf_le hbdd hs₂
    have hTs₂' : T < s₂ := lt_of_le_of_ne hTs₂ (fun h => hs₂.2.1 (by rw [← h]; exact hBT))
    set s₁ := max a (T - ε / 2) with hs₁
    have h1 : T - ε < s₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have h2 : s₁ < T := max_lt hTa (by linarith)
    have hBs₁ : V.detB s₁ ≠ 0 := hiso s₁ h2.ne (by rw [abs_lt]; constructor <;> linarith)
    have hμ1 := hbefore s₁ ⟨le_max_left _ _, by linarith⟩ h2 hBs₁
    have hμ12 := hjump s₁ s₂ h1 h2 hTs₂' hs₂T
    linarith [hs₂.2.2]
  · obtain ⟨ε, hε, hconst⟩ := const_near hV hBT
    obtain ⟨s, hs, hsT⟩ := hafter ε hε
    have hTs : T ≤ s := csInf_le hbdd hs
    have hsd : |s - T| < ε := by rw [abs_lt]; constructor <;> linarith
    have hμs := (hconst s hsd).2
    have hμT : V.μ T < V.μ a := by rw [← hμs]; exact hs.2.2
    rcases haT.lt_or_eq with hlt | heq
    · set s' := max a (T - ε / 2) with hs'
      have hs'1 : a ≤ s' := le_max_left _ _
      have hs'2 : s' < T := max_lt hlt (by linarith)
      have hs'3 : |s' - T| < ε := by
        rw [abs_lt]; constructor
        · linarith [le_max_right a (T - ε / 2)]
        · linarith
      obtain ⟨hBs', hμs'⟩ := hconst s' hs'3
      have := hbefore s' ⟨hs'1, by linarith⟩ hs'2 hBs'
      rw [hμs'] at this
      linarith
    · rw [← heq] at hμT
      exact lt_irrefl _ hμT

/-- From a non-crossing start, the vertical angle loses less than `3π`. -/
lemma psi_bound_from (hV : V.Good) {a b : ℝ} (hab : a ≤ b) (hB : V.detB a ≠ 0) :
    V.ψ a - 3 * Real.pi < V.ψ b := by
  have hmono := mu_mono hV (b := b) hB
  obtain ⟨-, hca⟩ := mu_facts hV hB
  rw [abs_lt] at hca
  by_cases hBb : V.detB b = 0
  · have hab' : a < b := lt_of_le_of_ne hab (fun h => hB (by rw [h]; exact hBb))
    obtain ⟨ε, hε, hiso, -⟩ := jump hV hBb
    obtain ⟨ε', hε', hψc⟩ := Metric.eventually_nhds_iff.mp
      (hV.ψ_cont.continuousAt (x := b) (Metric.ball_mem_nhds _ Real.pi_pos))
    have hm : 0 < min ε ε' := lt_min hε hε'
    set s := max a (b - min ε ε' / 2) with hs
    have hs1 : a ≤ s := le_max_left _ _
    have hs2 : s < b := max_lt hab' (by linarith)
    have hsd : |s - b| < min ε ε' := by
      rw [abs_lt]; constructor
      · linarith [le_max_right a (b - min ε ε' / 2)]
      · linarith
    have hBs : V.detB s ≠ 0 := hiso s hs2.ne (lt_of_lt_of_le hsd (min_le_left _ _))
    have hψs := hψc (show dist s b < ε' by
      rw [Real.dist_eq]; exact lt_of_lt_of_le hsd (min_le_right _ _))
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hψs
    obtain ⟨-, hcs⟩ := mu_facts hV hBs
    rw [abs_lt] at hcs
    have := hmono s ⟨hs1, hs2.le⟩ hBs
    linarith
  · obtain ⟨-, hcb⟩ := mu_facts hV hBb
    rw [abs_lt] at hcb
    have := hmono b ⟨hab, le_refl b⟩ hBb
    linarith [Real.pi_pos]

/-- The vertical angle loses less than `4π` over any time interval. -/
theorem psi_bound (hV : V.Good) {a b : ℝ} (hab : a ≤ b) :
    V.ψ a - 4 * Real.pi < V.ψ b := by
  by_cases hB : V.detB a = 0
  · rcases hab.lt_or_eq with hlt | heq
    · obtain ⟨ε, hε, hiso, -⟩ := jump hV hB
      obtain ⟨ε', hε', hψc⟩ := Metric.eventually_nhds_iff.mp
        (hV.ψ_cont.continuousAt (x := a) (Metric.ball_mem_nhds _ Real.pi_pos))
      set δ := min (min ε ε') (b - a) with hδ
      have hδpos : 0 < δ := lt_min (lt_min hε hε') (by linarith)
      set a' := a + δ / 2 with ha'
      have ha'1 : a < a' := by linarith
      have ha'2 : a' ≤ b := by linarith [min_le_right (min ε ε') (b - a)]
      have hd : |a' - a| < min ε ε' := by
        rw [abs_lt]; constructor
        · linarith [lt_min hε hε']
        · linarith [min_le_left (min ε ε') (b - a)]
      have hBa' : V.detB a' ≠ 0 := hiso a' ha'1.ne' (lt_of_lt_of_le hd (min_le_left _ _))
      have hψa' := hψc (show dist a' a < ε' by
        rw [Real.dist_eq]; exact lt_of_lt_of_le hd (min_le_right _ _))
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hψa'
      have := psi_bound_from hV ha'2 hBa'
      linarith
    · rw [heq]; linarith [Real.pi_pos]
  · have := psi_bound_from hV hab hB
    linarith [Real.pi_pos]

end VD

/-- Real form of the accretivity estimate for a `2 × 2` determinant. -/
private lemma accretive_real {a₁ a₂ d₁ d₂ p q r s : ℝ} (h1 : 0 < a₁)
    (h2 : (p + r) ^ 2 + (q - s) ^ 2 < 4 * a₁ * d₁)
    (him : a₁ * d₂ + a₂ * d₁ - (p * s + q * r) = 0) :
    0 < a₁ * d₁ - a₂ * d₂ - (p * r - q * s) := by
  have hid : a₁ ^ 2 * (a₁ * d₁ - a₂ * d₂ - (p * r - q * s)) =
      (a₁ ^ 2 + a₂ ^ 2) * (a₁ * d₁ - ((p + r) ^ 2 + (q - s) ^ 2) / 4) +
      (a₁ * (q + s) / 2 - a₂ * (p + r) / 2) ^ 2 +
      (a₁ * (-(p - r)) / 2 - a₂ * (q - s) / 2) ^ 2 -
      a₁ * a₂ * (a₁ * d₂ + a₂ * d₁ - (p * s + q * r)) := by ring
  rw [him, mul_zero, sub_zero] at hid
  have hdet : 0 < a₁ * d₁ - ((p + r) ^ 2 + (q - s) ^ 2) / 4 := by linarith
  have hsq : 0 < a₁ ^ 2 + a₂ ^ 2 := by positivity
  have hpos : 0 < a₁ ^ 2 * (a₁ * d₁ - a₂ * d₂ - (p * r - q * s)) := by
    rw [hid]; positivity
  exact pos_of_mul_pos_right hpos (by positivity)

/-- A `2 × 2` complex matrix with positive definite Hermitian part has its
determinant in the slit plane. -/
private lemma det_slit_of_accretive (x00 x01 x10 x11 : ℂ) (h1 : 0 < x00.re)
    (h2 : (x01.re + x10.re) ^ 2 + (x01.im - x10.im) ^ 2 < 4 * x00.re * x11.re) :
    x00 * x11 - x01 * x10 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  by_cases him : x00.re * x11.im + x00.im * x11.re -
      (x01.re * x10.im + x01.im * x10.re) = 0
  · left
    have := accretive_real h1 h2 him
    linarith
  · right
    intro h; apply him; linarith

/-- For the blocks `A, B, C, D` of a real symplectic `4 × 4` matrix, the vertical
determinant `det (B - i D)` times the conjugate of the ambient determinant
`det P`, with the sign changed, lies in the slit plane. The hypotheses are the
row relations `A Bᵀ = B Aᵀ`, `C Dᵀ = D Cᵀ`, `A Dᵀ - B Cᵀ = I`. -/
private lemma ratio_slit {a00 a01 a10 a11 b00 b01 b10 b11 c00 c01 c10 c11
    d00 d01 d10 d11 : ℝ}
    (hAB : a00 * b10 + a01 * b11 = b00 * a10 + b01 * a11)
    (hCD : c00 * d10 + c01 * d11 = d00 * c10 + d01 * c11)
    (h00 : a00 * d00 + a01 * d01 - (b00 * c00 + b01 * c01) = 1)
    (h01 : a00 * d10 + a01 * d11 - (b00 * c10 + b01 * c11) = 0)
    (h10 : a10 * d00 + a11 * d01 - (b10 * c00 + b11 * c01) = 0)
    (h11 : a10 * d10 + a11 * d11 - (b10 * c10 + b11 * c11) = 1) :
    -((⟨(b00 * b11 - b01 * b10) - (d00 * d11 - d01 * d10),
        -(b11 * d00 - b01 * d10 - b10 * d01 + b00 * d11)⟩ : ℂ) *
      (starRingEnd ℂ) ((⟨(a00 + d00) / 2, (b00 - c00) / 2⟩ : ℂ) *
          ⟨(a11 + d11) / 2, (b11 - c11) / 2⟩ -
        (⟨(a01 + d01) / 2, (b01 - c01) / 2⟩ : ℂ) *
          ⟨(a10 + d10) / 2, (b10 - c10) / 2⟩)) ∈ Complex.slitPlane := by
  -- entries of `X = (D + i B) P^*`
  set x00 : ℂ := ⟨(d00 * (a00 + d00) + b00 * (b00 - c00) + d01 * (a01 + d01) +
      b01 * (b01 - c01)) / 2, (b00 * (a00 + d00) - d00 * (b00 - c00) +
      b01 * (a01 + d01) - d01 * (b01 - c01)) / 2⟩ with hx00
  set x01 : ℂ := ⟨(d00 * (a10 + d10) + b00 * (b10 - c10) + d01 * (a11 + d11) +
      b01 * (b11 - c11)) / 2, (b00 * (a10 + d10) - d00 * (b10 - c10) +
      b01 * (a11 + d11) - d01 * (b11 - c11)) / 2⟩ with hx01
  set x10 : ℂ := ⟨(d10 * (a00 + d00) + b10 * (b00 - c00) + d11 * (a01 + d01) +
      b11 * (b01 - c01)) / 2, (b10 * (a00 + d00) - d10 * (b00 - c00) +
      b11 * (a01 + d01) - d11 * (b01 - c01)) / 2⟩ with hx10
  set x11 : ℂ := ⟨(d10 * (a10 + d10) + b10 * (b10 - c10) + d11 * (a11 + d11) +
      b11 * (b11 - c11)) / 2, (b10 * (a10 + d10) - d10 * (b10 - c10) +
      b11 * (a11 + d11) - d11 * (b11 - c11)) / 2⟩ with hx11
  have hdet : -((⟨(b00 * b11 - b01 * b10) - (d00 * d11 - d01 * d10),
        -(b11 * d00 - b01 * d10 - b10 * d01 + b00 * d11)⟩ : ℂ) *
      (starRingEnd ℂ) ((⟨(a00 + d00) / 2, (b00 - c00) / 2⟩ : ℂ) *
          ⟨(a11 + d11) / 2, (b11 - c11) / 2⟩ -
        (⟨(a01 + d01) / 2, (b01 - c01) / 2⟩ : ℂ) *
          ⟨(a10 + d10) / 2, (b10 - c10) / 2⟩)) = x00 * x11 - x01 * x10 := by
    apply Complex.ext <;>
      simp only [hx00, hx01, hx10, hx11, Complex.neg_re, Complex.neg_im, Complex.mul_re,
        Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im] <;>
      ring
  rw [hdet]
  apply det_slit_of_accretive
  · have e1 : 2 * x00.re = 1 + (d00 ^ 2 + b00 ^ 2 + d01 ^ 2 + b01 ^ 2) := by
      simp only [hx00]; linear_combination h00
    nlinarith [sq_nonneg d00, sq_nonneg b00, sq_nonneg d01, sq_nonneg b01]
  · have e1 : 2 * x00.re = 1 + (d00 ^ 2 + b00 ^ 2 + d01 ^ 2 + b01 ^ 2) := by
      simp only [hx00]; linear_combination h00
    have e2 : 2 * x11.re = 1 + (d10 ^ 2 + b10 ^ 2 + d11 ^ 2 + b11 ^ 2) := by
      simp only [hx11]; linear_combination h11
    have e3 : x01.re + x10.re = d00 * d10 + b00 * b10 + d01 * d11 + b01 * b11 := by
      simp only [hx01, hx10]; linear_combination (1 / 2 : ℝ) * h01 + (1 / 2 : ℝ) * h10
    have e4 : x01.im - x10.im = b00 * d10 - d00 * b10 + b01 * d11 - d01 * b11 := by
      simp only [hx01, hx10]
      linear_combination (-1 / 2 : ℝ) * hAB - (1 / 2 : ℝ) * hCD
    rw [e3, e4]
    have hlag : (d00 ^ 2 + b00 ^ 2 + d01 ^ 2 + b01 ^ 2) *
        (d10 ^ 2 + b10 ^ 2 + d11 ^ 2 + b11 ^ 2) -
        ((d00 * d10 + b00 * b10 + d01 * d11 + b01 * b11) ^ 2 +
          (b00 * d10 - d00 * b10 + b01 * d11 - d01 * b11) ^ 2) =
        (-b00 * b11 + b01 * b10 + d00 * d11 - d01 * d10) ^ 2 +
          (b00 * d11 - b01 * d10 - b10 * d01 + b11 * d00) ^ 2 := by ring
    have h4 : 4 * x00.re * x11.re =
        (1 + (d00 ^ 2 + b00 ^ 2 + d01 ^ 2 + b01 ^ 2)) *
          (1 + (d10 ^ 2 + b10 ^ 2 + d11 ^ 2 + b11 ^ 2)) := by
      rw [show 4 * x00.re * x11.re = (2 * x00.re) * (2 * x11.re) by ring, e1, e2]
    rw [h4]
    nlinarith [sq_nonneg (-b00 * b11 + b01 * b10 + d00 * d11 - d01 * d10),
      sq_nonneg (b00 * d11 - b01 * d10 - b10 * d01 + b11 * d00),
      sq_nonneg d00, sq_nonneg b00, sq_nonneg d01, sq_nonneg b01,
      sq_nonneg d10, sq_nonneg b10, sq_nonneg d11, sq_nonneg b11]

/-- The symplectic form in the coordinates `(q₁,q₂,p₁,p₂)`. -/
private def omega (u v : Phase) : ℝ := u 0 * v 2 - u 2 * v 0 + u 1 * v 3 - u 3 * v 1

private lemma basis_decomp (v : Phase) :
    v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3 := by
  funext i; fin_cases i <;> simp [coordinateVector]

/-- A linear functional on `Phase` expands along the coordinate basis. -/
private lemma clm_expand (L : Phase →L[ℝ] ℝ) (v : Phase) :
    L v = v 0 * L (coordinateVector 0) + v 1 * L (coordinateVector 1) +
      v 2 * L (coordinateVector 2) + v 3 * L (coordinateVector 3) := by
  conv_lhs => rw [basis_decomp v]
  simp only [map_add, map_smul, smul_eq_mul]

/-- A bilinear form on `Phase` expands along the basis in its first slot. -/
private lemma clm2_expand (H : Phase →L[ℝ] Phase →L[ℝ] ℝ) (v w : Phase) :
    H v w = v 0 * H (coordinateVector 0) w + v 1 * H (coordinateVector 1) w +
      v 2 * H (coordinateVector 2) w + v 3 * H (coordinateVector 3) w := by
  conv_lhs => rw [basis_decomp v]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private lemma two_le_infty : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top

/-- Symmetry of the Hessian of a smooth function. -/
private lemma hess_symm {F : Phase → ℝ} {p : Phase} (hF : ContDiffAt ℝ ∞ F p) (v w : Phase) :
    fderiv ℝ (fderiv ℝ F) p v w = fderiv ℝ (fderiv ℝ F) p w v :=
  hF.isSymmSndFDerivAt two_le_infty v w

/-- Directional derivatives of a smooth function are differentiable, with the
Hessian as derivative. -/
private lemma partial_hasFDerivAt {F : Phase → ℝ} {p : Phase} (hF : ContDiffAt ℝ ∞ F p)
    (v : Phase) :
    HasFDerivAt (fun s => fderiv ℝ F s v) ((fderiv ℝ (fderiv ℝ F) p).flip v) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hF.fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact WithTop.coe_le_coe.2 le_top)
      ).differentiableAt one_ne_zero
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  simpa using h

/-- The derivative of the Hamiltonian vector field is `I` times the Hessian. -/
private lemma hvf_hasFDerivAt {F : Phase → ℝ} {p : Phase} (hF : ContDiffAt ℝ ∞ F p) :
    HasFDerivAt (hamiltonianVectorField F)
      (ContinuousLinearMap.pi ![(fderiv ℝ (fderiv ℝ F) p).flip (coordinateVector 2),
        (fderiv ℝ (fderiv ℝ F) p).flip (coordinateVector 3),
        -(fderiv ℝ (fderiv ℝ F) p).flip (coordinateVector 0),
        -(fderiv ℝ (fderiv ℝ F) p).flip (coordinateVector 1)]) p := by
  rw [hasFDerivAt_pi']
  intro i
  rw [ContinuousLinearMap.proj_pi]
  fin_cases i
  · exact partial_hasFDerivAt hF (coordinateVector 2)
  · exact partial_hasFDerivAt hF (coordinateVector 3)
  · exact (partial_hasFDerivAt hF (coordinateVector 0)).neg
  · exact (partial_hasFDerivAt hF (coordinateVector 1)).neg

private lemma hvf_fderiv_apply {F : Phase → ℝ} {p : Phase} (hF : ContDiffAt ℝ ∞ F p)
    (w : Phase) :
    fderiv ℝ (hamiltonianVectorField F) p w 0 =
        fderiv ℝ (fderiv ℝ F) p w (coordinateVector 2) ∧
      fderiv ℝ (hamiltonianVectorField F) p w 1 =
        fderiv ℝ (fderiv ℝ F) p w (coordinateVector 3) ∧
      fderiv ℝ (hamiltonianVectorField F) p w 2 =
        -fderiv ℝ (fderiv ℝ F) p w (coordinateVector 0) ∧
      fderiv ℝ (hamiltonianVectorField F) p w 3 =
        -fderiv ℝ (fderiv ℝ F) p w (coordinateVector 1) := by
  rw [(hvf_hasFDerivAt hF).fderiv]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- The linearized Hamiltonian field is infinitesimally symplectic. -/
private lemma omega_A {F : Phase → ℝ} {p : Phase} (hF : ContDiffAt ℝ ∞ F p) (a b : Phase) :
    omega (fderiv ℝ (hamiltonianVectorField F) p a) b +
      omega a (fderiv ℝ (hamiltonianVectorField F) p b) = 0 := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := hvf_fderiv_apply hF a
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hvf_fderiv_apply hF b
  unfold omega
  rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
  have h1 := clm_expand (fderiv ℝ (fderiv ℝ F) p a) b
  have h2 := clm_expand (fderiv ℝ (fderiv ℝ F) p b) a
  have hs := hess_symm hF a b
  linear_combination -h1 + h2 + hs

/-- The variational solution moves vectors by the linearized field. -/
private lemma var_hasDerivAt {F : Phase → ℝ} {x : ℝ → Phase} {Y : ℝ → (Phase →L[ℝ] Phase)}
    (hY : IsHamiltonianVariationalSolution F x Y) (w : Phase) (s : ℝ) :
    HasDerivAt (fun s => Y s w) (fderiv ℝ (hamiltonianVectorField F) (x s) (Y s w)) s := by
  have h := (hY.2 s).clm_apply (hasDerivAt_const s w)
  simpa using h

/-- The variational solution is symplectic. -/
private lemma symplectic_flow {F : Phase → ℝ} {x : ℝ → Phase} {Y : ℝ → (Phase →L[ℝ] Phase)}
    (hF : ∀ t, ContDiffAt ℝ ∞ F (x t)) (hY : IsHamiltonianVariationalSolution F x Y)
    (t : ℝ) (u v : Phase) : omega (Y t u) (Y t v) = omega u v := by
  have hderiv : ∀ s, HasDerivAt (fun s => omega (Y s u) (Y s v)) 0 s := by
    intro s
    have hc := hasDerivAt_pi.mp (var_hasDerivAt hY u s)
    have hd := hasDerivAt_pi.mp (var_hasDerivAt hY v s)
    have h := ((((hc 0).mul (hd 2)).sub ((hc 2).mul (hd 0))).add ((hc 1).mul (hd 3))).sub
      ((hc 3).mul (hd 1))
    have h0 := omega_A (hF s) (Y s u) (Y s v)
    unfold omega at h0
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    · linear_combination h0
    · simp [omega]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) t 0
  rw [hconst, hY.1]
  rfl

/-- The standard symplectic matrix, `ω(u, v) = uᵀ Jm v`. -/
private def Jm : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

/-- The column relations `M.transpose Jm M = Jm` imply the row relations `M Jm M.transpose = Jm`. -/
private lemma row_relations (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hcol : ∀ k l : Fin 4,
      M 0 k * M 2 l - M 2 k * M 0 l + M 1 k * M 3 l - M 3 k * M 1 l = Jm k l) :
    ∀ i j : Fin 4, M i 0 * M j 2 + M i 1 * M j 3 - M i 2 * M j 0 - M i 3 * M j 1 = Jm i j := by
  have hJJ : Jm * Jm = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_four]
  have h1 : M.transpose * Jm * M = Jm := by
    ext k l
    rw [← hcol k l]
    simp [Matrix.mul_apply, Fin.sum_univ_four, Jm]
    ring
  have h2 : (-(Jm * M.transpose * Jm)) * M = 1 := by
    calc (-(Jm * M.transpose * Jm)) * M = -(Jm * (M.transpose * Jm * M)) := by
          simp [Matrix.mul_assoc]
      _ = -(Jm * Jm) := by rw [h1]
      _ = 1 := by rw [hJJ, neg_neg]
  have h3 : M * (-(Jm * M.transpose * Jm)) = 1 := mul_eq_one_comm.mp h2
  have h4 : M * Jm * M.transpose * Jm = -1 := by
    calc M * Jm * M.transpose * Jm = -(M * (-(Jm * M.transpose * Jm))) := by simp [Matrix.mul_assoc]
      _ = -1 := by rw [h3]
  have h5 : M * Jm * M.transpose = Jm := by
    calc M * Jm * M.transpose = -(M * Jm * M.transpose * Jm * Jm) := by
          rw [Matrix.mul_assoc (M * Jm * M.transpose) Jm Jm, hJJ]; simp
      _ = Jm := by rw [h4]; simp
  intro i j
  have := congrFun (congrFun h5 i) j
  rw [← this]
  simp [Matrix.mul_apply, Fin.sum_univ_four, Jm]
  ring

/-- The ambient determinant in terms of the matrix entries. -/
private lemma ambientRotationDet_eq (M : Phase →L[ℝ] Phase) :
    ambientRotationDet M =
      (⟨(M (coordinateVector 0) 0 + M (coordinateVector 2) 2) / 2,
          (M (coordinateVector 2) 0 - M (coordinateVector 0) 2) / 2⟩ : ℂ) *
        ⟨(M (coordinateVector 1) 1 + M (coordinateVector 3) 3) / 2,
          (M (coordinateVector 3) 1 - M (coordinateVector 1) 3) / 2⟩ -
      (⟨(M (coordinateVector 1) 0 + M (coordinateVector 3) 2) / 2,
          (M (coordinateVector 3) 0 - M (coordinateVector 1) 2) / 2⟩ : ℂ) *
        ⟨(M (coordinateVector 0) 1 + M (coordinateVector 2) 3) / 2,
          (M (coordinateVector 2) 1 - M (coordinateVector 0) 3) / 2⟩ := by
  unfold ambientRotationDet
  rw [Matrix.det_fin_two]
  rfl

/-- If `-(G conj q)` lies in the slit plane and `q = ρ e^{iα}`, then
`α + arg (-(G conj q)) + π` is an argument of `G`. -/
private lemma polar_of_ratio {G q : ℂ} {α ρ : ℝ} (hρ : 0 < ρ)
    (hq : q = ⟨ρ * Real.cos α, ρ * Real.sin α⟩) :
    G.re = ‖G‖ * Real.cos (α + Complex.arg (-(G * (starRingEnd ℂ) q)) + Real.pi) ∧
      G.im = ‖G‖ * Real.sin (α + Complex.arg (-(G * (starRingEnd ℂ) q)) + Real.pi) := by
  set ξ := -(G * (starRingEnd ℂ) q) with hξ
  set δ := Complex.arg ξ with hδ
  have hre := Complex.norm_mul_cos_arg ξ
  have him := Complex.norm_mul_sin_arg ξ
  have hsc := Real.sin_sq_add_cos_sq α
  have hqn : ‖q‖ = ρ := by
    have h2 : ‖q‖ ^ 2 = ρ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hq]
      linear_combination ρ ^ 2 * hsc
    exact (pow_left_inj₀ (norm_nonneg _) hρ.le two_ne_zero).mp h2
  have hξn : ‖ξ‖ = ‖G‖ * ρ := by
    rw [hξ, norm_neg, norm_mul, Complex.norm_conj, hqn]
  have hξre : ξ.re = -(G.re * (ρ * Real.cos α) + G.im * (ρ * Real.sin α)) := by
    rw [hξ, hq]; simp [Complex.mul_re]
  have hξim : ξ.im = -(G.im * (ρ * Real.cos α) - G.re * (ρ * Real.sin α)) := by
    rw [hξ, hq]; simp [Complex.mul_im]; ring
  constructor
  · have key : ρ * (‖G‖ * Real.cos (α + δ + Real.pi)) = ρ * G.re := by
      rw [Real.cos_add_pi, Real.cos_add]
      have e : ρ * (‖G‖ * -(Real.cos α * Real.cos δ - Real.sin α * Real.sin δ)) =
          -(Real.cos α * (‖ξ‖ * Real.cos δ) - Real.sin α * (‖ξ‖ * Real.sin δ)) := by
        rw [hξn]; ring
      rw [e, hre, him, hξre, hξim]
      linear_combination (ρ * G.re) * hsc
    exact (mul_left_cancel₀ hρ.ne' key).symm
  · have key : ρ * (‖G‖ * Real.sin (α + δ + Real.pi)) = ρ * G.im := by
      rw [Real.sin_add_pi, Real.sin_add]
      have e : ρ * (‖G‖ * -(Real.sin α * Real.cos δ + Real.cos α * Real.sin δ)) =
          -(Real.sin α * (‖ξ‖ * Real.cos δ) + Real.cos α * (‖ξ‖ * Real.sin δ)) := by
        rw [hξn]; ring
      rw [e, hre, him, hξre, hξim]
      linear_combination (ρ * G.im) * hsc
    exact (mul_left_cancel₀ hρ.ne' key).symm

private lemma continuous_mk {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => (⟨f t, g t⟩ : ℂ)) := by
  have : (fun t => (⟨f t, g t⟩ : ℂ)) = fun t => (f t : ℂ) + (g t : ℂ) * Complex.I := by
    funext t; apply Complex.ext <;> simp
  rw [this]
  exact (Complex.continuous_ofReal.comp hf).add
    ((Complex.continuous_ofReal.comp hg).mul continuous_const)

private lemma VD.g_eq_mk (V : VD) (t : ℝ) :
    V.g t = ⟨V.detB t - V.detD t, -V.trN t⟩ := by
  apply Complex.ext <;> simp [VD.g]

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Phase → ℝ) (x : ℝ → Phase),
        (∀ t : ℝ, ContDiffAt ℝ ∞ F (x t)) →
        (∀ t : ℝ, HasDerivAt x (hamiltonianVectorField F (x t)) t) →
        (∀ (t : ℝ) (v : Phase), v ≠ 0 → v 0 = 0 → v 1 = 0 →
          0 < fderiv ℝ (fun s => fderiv ℝ F s v) (x t) v) →
        ∀ Y : ℝ → (Phase →L[ℝ] Phase),
          IsHamiltonianVariationalSolution F x Y →
          ∀ α : ℝ → ℝ, IsAmbientRotationAngle Y α →
            ∀ a b : ℝ, a ≤ b → -C ≤ α b - α a := by
  refine ⟨6 * Real.pi, by positivity, ?_⟩
  intro F x hF _hx hpos Y hY α hα a b hab
  -- entries of the variational solution and of the Hessian
  set H : ℝ → Phase →L[ℝ] Phase →L[ℝ] ℝ := fun t => fderiv ℝ (fderiv ℝ F) (x t) with hH
  have hcomp : ∀ (k : Fin 4) (i : Fin 4) (t : ℝ), HasDerivAt
      (fun s => Y s (coordinateVector k) i)
      (fderiv ℝ (hamiltonianVectorField F) (x t) (Y t (coordinateVector k)) i) t :=
    fun k i t => hasDerivAt_pi.mp (var_hasDerivAt hY (coordinateVector k) t) i
  have hcont : ∀ (k i : Fin 4), Continuous (fun s => Y s (coordinateVector k) i) :=
    fun k i => continuous_iff_continuousAt.2 fun t => (hcomp k i t).continuousAt
  -- Hessian facts along the trajectory
  have hHv : ∀ t v, fderiv ℝ (fun s => fderiv ℝ F s v) (x t) v = H t v v := by
    intro t v
    rw [(partial_hasFDerivAt (hF t) v).fderiv]
    simp [hH]
  have hsym : ∀ t v w, H t v w = H t w v := fun t v w => hess_symm (hF t) v w
  let V₀ : VD :=
    { b00 := fun t => Y t (coordinateVector 2) 0, b01 := fun t => Y t (coordinateVector 3) 0,
      b10 := fun t => Y t (coordinateVector 2) 1, b11 := fun t => Y t (coordinateVector 3) 1,
      d00 := fun t => Y t (coordinateVector 2) 2, d01 := fun t => Y t (coordinateVector 3) 2,
      d10 := fun t => Y t (coordinateVector 2) 3, d11 := fun t => Y t (coordinateVector 3) 3,
      s02 := fun t => H t (coordinateVector 0) (coordinateVector 2),
      s12 := fun t => H t (coordinateVector 1) (coordinateVector 2),
      s22 := fun t => H t (coordinateVector 2) (coordinateVector 2),
      s23 := fun t => H t (coordinateVector 2) (coordinateVector 3),
      s03 := fun t => H t (coordinateVector 0) (coordinateVector 3),
      s13 := fun t => H t (coordinateVector 1) (coordinateVector 3),
      s33 := fun t => H t (coordinateVector 3) (coordinateVector 3),
      ψ := fun _ => 0 }
  set q : ℝ → ℂ := fun t => ambientRotationDet (Y t) with hq
  -- the vertical determinant times the conjugate ambient determinant avoids `[0, ∞)`
  have hslit : ∀ t, -(V₀.g t * (starRingEnd ℂ) (q t)) ∈ Complex.slitPlane := by
    intro t
    set Mt : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i k => Y t (coordinateVector k) i
      with hMt
    have hcol : ∀ k l : Fin 4,
        Mt 0 k * Mt 2 l - Mt 2 k * Mt 0 l + Mt 1 k * Mt 3 l - Mt 3 k * Mt 1 l = Jm k l := by
      intro k l
      have hs := symplectic_flow hF hY t (coordinateVector k) (coordinateVector l)
      unfold omega at hs
      simp only [hMt, Matrix.of_apply]
      rw [hs]
      fin_cases k <;> fin_cases l <;> simp [coordinateVector, Jm]
    have hrow := row_relations Mt hcol
    have hAB := hrow 0 1
    have hCD := hrow 2 3
    have h00 := hrow 0 2
    have h01 := hrow 0 3
    have h10 := hrow 1 2
    have h11 := hrow 1 3
    have hJ01 : Jm 0 1 = 0 := by simp [Jm]
    have hJ23 : Jm 2 3 = 0 := by simp [Jm]
    have hJ02 : Jm 0 2 = 1 := by simp [Jm]
    have hJ03 : Jm 0 3 = 0 := by simp [Jm]
    have hJ12 : Jm 1 2 = 0 := by simp [Jm]
    have hJ13 : Jm 1 3 = 1 := by simp [Jm]
    rw [hJ01] at hAB; rw [hJ23] at hCD; rw [hJ02] at h00; rw [hJ03] at h01
    rw [hJ12] at h10; rw [hJ13] at h11
    simp only [hMt, Matrix.of_apply] at hAB hCD h00 h01 h10 h11
    have hr := ratio_slit (a00 := Y t (coordinateVector 0) 0) (a01 := Y t (coordinateVector 1) 0)
      (a10 := Y t (coordinateVector 0) 1) (a11 := Y t (coordinateVector 1) 1)
      (b00 := Y t (coordinateVector 2) 0) (b01 := Y t (coordinateVector 3) 0)
      (b10 := Y t (coordinateVector 2) 1) (b11 := Y t (coordinateVector 3) 1)
      (c00 := Y t (coordinateVector 0) 2) (c01 := Y t (coordinateVector 1) 2)
      (c10 := Y t (coordinateVector 0) 3) (c11 := Y t (coordinateVector 1) 3)
      (d00 := Y t (coordinateVector 2) 2) (d01 := Y t (coordinateVector 3) 2)
      (d10 := Y t (coordinateVector 2) 3) (d11 := Y t (coordinateVector 3) 3)
      (by linear_combination hAB) (by linear_combination hCD) (by linear_combination h00)
      (by linear_combination h01) (by linear_combination h10) (by linear_combination h11)
    have hg : V₀.g t = ⟨(Y t (coordinateVector 2) 0 * Y t (coordinateVector 3) 1 -
        Y t (coordinateVector 3) 0 * Y t (coordinateVector 2) 1) -
        (Y t (coordinateVector 2) 2 * Y t (coordinateVector 3) 3 -
          Y t (coordinateVector 3) 2 * Y t (coordinateVector 2) 3),
        -(Y t (coordinateVector 3) 1 * Y t (coordinateVector 2) 2 -
          Y t (coordinateVector 3) 0 * Y t (coordinateVector 2) 3 -
          Y t (coordinateVector 2) 1 * Y t (coordinateVector 3) 2 +
          Y t (coordinateVector 2) 0 * Y t (coordinateVector 3) 3)⟩ := by
      rw [VD.g_eq_mk]
      apply Complex.ext <;> simp [V₀, VD.detB, VD.detD, VD.trN, VD.n00, VD.n11] <;> ring
    rw [hg, hq]
    simp only
    rw [ambientRotationDet_eq]
    exact hr
  -- the vertical angle
  set δ : ℝ → ℝ := fun t => Complex.arg (-(V₀.g t * (starRingEnd ℂ) (q t))) with hδ
  have hgcont : Continuous V₀.g := by
    have : V₀.g = fun t => (⟨V₀.detB t - V₀.detD t, -V₀.trN t⟩ : ℂ) := by
      funext t; exact VD.g_eq_mk V₀ t
    rw [this]
    apply continuous_mk
    · simp only [V₀, VD.detB, VD.detD]
      fun_prop
    · simp only [V₀, VD.trN, VD.n00, VD.n11]
      fun_prop
  have hqcont : Continuous q := by
    have : q = fun t => ambientRotationDet (Y t) := rfl
    rw [this]
    simp only [ambientRotationDet_eq]
    refine ((continuous_mk ?_ ?_).mul (continuous_mk ?_ ?_)).sub
      ((continuous_mk ?_ ?_).mul (continuous_mk ?_ ?_)) <;> fun_prop
  have hδcont : Continuous δ := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (f := fun s => -(V₀.g s * (starRingEnd ℂ) (q s)))
      (Complex.continuousAt_arg (hslit t))
      ((hgcont.mul (Complex.continuous_conj.comp hqcont)).neg.continuousAt)
  let V : VD := { V₀ with ψ := fun t => α t + δ t + Real.pi }
  have hV : V.Good := by
    have hbd : ∀ (j : Fin 4) (t : ℝ), (j = 2 ∨ j = 3) →
        fderiv ℝ (hamiltonianVectorField F) (x t) (Y t (coordinateVector j)) 0 =
          Y t (coordinateVector j) 0 * H t (coordinateVector 0) (coordinateVector 2) +
          Y t (coordinateVector j) 1 * H t (coordinateVector 1) (coordinateVector 2) +
          Y t (coordinateVector j) 2 * H t (coordinateVector 2) (coordinateVector 2) +
          Y t (coordinateVector j) 3 * H t (coordinateVector 2) (coordinateVector 3) ∧
        fderiv ℝ (hamiltonianVectorField F) (x t) (Y t (coordinateVector j)) 1 =
          Y t (coordinateVector j) 0 * H t (coordinateVector 0) (coordinateVector 3) +
          Y t (coordinateVector j) 1 * H t (coordinateVector 1) (coordinateVector 3) +
          Y t (coordinateVector j) 2 * H t (coordinateVector 2) (coordinateVector 3) +
          Y t (coordinateVector j) 3 * H t (coordinateVector 3) (coordinateVector 3) := by
      intro j t _
      obtain ⟨h0, h1, -, -⟩ := hvf_fderiv_apply (hF t) (Y t (coordinateVector j))
      refine ⟨?_, ?_⟩
      · rw [h0, clm2_expand, ← hsym t (coordinateVector 2) (coordinateVector 3)]
      · rw [h1, clm2_expand]
    refine
      { hb00 := fun t => (hcomp 2 0 t).congr_deriv ((hbd 2 t (Or.inl rfl)).1)
        hb01 := fun t => (hcomp 3 0 t).congr_deriv ((hbd 3 t (Or.inr rfl)).1)
        hb10 := fun t => (hcomp 2 1 t).congr_deriv ((hbd 2 t (Or.inl rfl)).2)
        hb11 := fun t => (hcomp 3 1 t).congr_deriv ((hbd 3 t (Or.inr rfl)).2)
        hd00 := fun t => (hcomp 2 2 t).differentiableAt
        hd01 := fun t => (hcomp 3 2 t).differentiableAt
        hd10 := fun t => (hcomp 2 3 t).differentiableAt
        hd11 := fun t => (hcomp 3 3 t).differentiableAt
        lag := ?_
        rank := ?_
        s22_pos := ?_
        sdet_pos := ?_
        ψ_cont := ?_
        polar_re := ?_
        polar_im := ?_ }
    · intro t
      have hs := symplectic_flow hF hY t (coordinateVector 2) (coordinateVector 3)
      unfold omega at hs
      simp [coordinateVector] at hs
      show Y t (coordinateVector 2) 0 * Y t (coordinateVector 3) 2 +
          Y t (coordinateVector 2) 1 * Y t (coordinateVector 3) 3 =
        Y t (coordinateVector 3) 0 * Y t (coordinateVector 2) 2 +
          Y t (coordinateVector 3) 1 * Y t (coordinateVector 2) 3
      linarith
    · intro t k0 k1 e0 e1 e2 e3
      replace e0 : Y t (coordinateVector 2) 0 * k0 + Y t (coordinateVector 3) 0 * k1 = 0 := e0
      replace e1 : Y t (coordinateVector 2) 1 * k0 + Y t (coordinateVector 3) 1 * k1 = 0 := e1
      replace e2 : Y t (coordinateVector 2) 2 * k0 + Y t (coordinateVector 3) 2 * k1 = 0 := e2
      replace e3 : Y t (coordinateVector 2) 3 * k0 + Y t (coordinateVector 3) 3 * k1 = 0 := e3
      set w : Phase := k0 • coordinateVector 2 + k1 • coordinateVector 3 with hw
      have hYw : Y t w = 0 := by
        rw [hw, map_add, map_smul, map_smul]
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        fin_cases i
        · show k0 * Y t (coordinateVector 2) 0 + k1 * Y t (coordinateVector 3) 0 = 0
          linear_combination e0
        · show k0 * Y t (coordinateVector 2) 1 + k1 * Y t (coordinateVector 3) 1 = 0
          linear_combination e1
        · show k0 * Y t (coordinateVector 2) 2 + k1 * Y t (coordinateVector 3) 2 = 0
          linear_combination e2
        · show k0 * Y t (coordinateVector 2) 3 + k1 * Y t (coordinateVector 3) 3 = 0
          linear_combination e3
      have hs0 := symplectic_flow hF hY t (coordinateVector 0) w
      have hs1 := symplectic_flow hF hY t (coordinateVector 1) w
      rw [hYw] at hs0 hs1
      simp [omega, hw, coordinateVector] at hs0 hs1
      exact ⟨hs0.symm, hs1.symm⟩
    · intro t
      have h := hpos t (coordinateVector 2) (fun h => by
        have := congrFun h 2; simp [coordinateVector] at this)
        (by simp [coordinateVector]) (by simp [coordinateVector])
      rw [hHv] at h
      exact h
    · intro t
      have hs22 : 0 < H t (coordinateVector 2) (coordinateVector 2) := by
        have h := hpos t (coordinateVector 2) (fun h => by
          have := congrFun h 2; simp [coordinateVector] at this)
          (by simp [coordinateVector]) (by simp [coordinateVector])
        rwa [hHv] at h
      set c2 := -H t (coordinateVector 2) (coordinateVector 3)
      set c3 := H t (coordinateVector 2) (coordinateVector 2)
      set v : Phase := c2 • coordinateVector 2 + c3 • coordinateVector 3 with hv
      have hv3 : v 3 = c3 := by simp [hv, coordinateVector]
      have hvne : v ≠ 0 := by
        intro h; have := congrFun h 3; rw [hv3] at this; simp at this; linarith
      have h := hpos t v hvne (by simp [hv, coordinateVector]) (by simp [hv, coordinateVector])
      rw [hHv] at h
      have hexp : H t v v = c2 ^ 2 * H t (coordinateVector 2) (coordinateVector 2) +
          c2 * c3 * (H t (coordinateVector 2) (coordinateVector 3) +
            H t (coordinateVector 3) (coordinateVector 2)) +
          c3 ^ 2 * H t (coordinateVector 3) (coordinateVector 3) := by
        rw [hv]
        simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      rw [hexp, ← hsym t (coordinateVector 2) (coordinateVector 3)] at h
      show 0 < H t (coordinateVector 2) (coordinateVector 2) *
          H t (coordinateVector 3) (coordinateVector 3) -
          H t (coordinateVector 2) (coordinateVector 3) ^ 2
      have hkey : c3 * (H t (coordinateVector 2) (coordinateVector 2) *
          H t (coordinateVector 3) (coordinateVector 3) -
          H t (coordinateVector 2) (coordinateVector 3) ^ 2) =
          c2 ^ 2 * H t (coordinateVector 2) (coordinateVector 2) +
          c2 * c3 * (H t (coordinateVector 2) (coordinateVector 3) +
            H t (coordinateVector 2) (coordinateVector 3)) +
          c3 ^ 2 * H t (coordinateVector 3) (coordinateVector 3) := by
        simp only [c2, c3]; ring
      rw [← hkey] at h
      exact pos_of_mul_pos_right h hs22.le
    · exact (hα.1.add hδcont).add continuous_const
    · intro t
      obtain ⟨ρ, hρ, hqt⟩ := hα.2 t
      exact (polar_of_ratio (G := V₀.g t) (q := q t) hρ hqt).1
    · intro t
      obtain ⟨ρ, hρ, hqt⟩ := hα.2 t
      exact (polar_of_ratio (G := V₀.g t) (q := q t) hρ hqt).2
  have hbound := VD.psi_bound hV hab
  have hδa := Complex.neg_pi_lt_arg (-(V₀.g a * (starRingEnd ℂ) (q a)))
  have hδb := Complex.arg_le_pi (-(V₀.g b * (starRingEnd ℂ) (q b)))
  change α a + δ a + Real.pi - 4 * Real.pi < α b + δ b + Real.pi at hbound
  simp only [hδ] at hbound
  linarith
