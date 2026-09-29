-- Prove2me | solution 1 for ExponentialSums.vdC_second_derivative
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T10:18:38.184983+00:00
-- url     : https://prove2.me/submissions/925f9478-52e9-4f1e-ab09-ac21322ba3f3

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.ExpSum.Kusmin =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The Kusmin–Landau inequality and van der Corput's second-derivative test

This file develops the B-side foundation of the van der Corput exponential-sum
toolkit: the **Kusmin–Landau inequality** (`kusmin_landau`) and the discrete
**second-derivative test** (`vdC_second_derivative`, milestone 2).

## House note on the character

A concurrent executor is building `Salt/ExpSum/Basic.lean` with an additive
character `eR (x : ℝ) : ℂ := Complex.exp (2πi x)` and its API.  To stay
independent this file defines a **private local copy** `eK` with the *same*
definition.  The house should **unify `eK` with `eR` at wire-in** — every use
of `eK` here is exactly `Complex.exp (2 * π * x * I)`.

## Milestone 1 — Kusmin–Landau

Stated discretely on the consecutive differences `g n := f (n+1) - f n`.

**Mathematical note (a real catch).**  The naive discrete hypothesis
"`Int.fract (g n) ∈ [δ, 1-δ]` and `g` monotone" is *insufficient*: without
pinning `g n` into a *single* unit interval the bound degrades to
`O((b-a)/δ)` (each integer that `g` crosses between samples costs `≍ 1/δ` of
total variation).  In the continuous Kusmin–Landau this cannot happen —
continuity + monotonicity + "bounded away from integers" force `g` to stay in
one interval `(m+δ, m+1-δ)`.  We therefore state the honest discrete shadow:
there is a fixed integer `m` with `g n ∈ [m+δ, m+1-δ]` throughout.  This is
exactly the window that milestone 2's decomposition produces, so the two
milestones are internally consistent.

Result: `‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 1 / δ`  (absolute constant `C = 1`).

The engine is the telescoping weight `w n := (1 - eK (g n))⁻¹`.  Its key
feature (`wK_re`) is that `Re (w n) = 1/2` is *constant*, so the Abel
differences `w (n+1) - w n` are purely imaginary and their total variation
telescopes through `Im (w n) = cot(π · g n)/2`, which is monotone because `g`
is monotone.
-/

namespace Salt.ExpSum

open Real Finset

/-- Private local additive character `eK x = exp(2πi x)`.  **Unify with
`Basic.eR` at wire-in** (identical definition). -/
noncomputable def eK (x : ℝ) : ℂ := Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I)

@[simp] lemma eK_norm (x : ℝ) : ‖eK x‖ = 1 := by
  simp only [eK]
  exact Complex.norm_exp_ofReal_mul_I _

lemma eK_add (x y : ℝ) : eK (x + y) = eK x * eK y := by
  simp only [eK, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- Periodicity: `eK` is unchanged by adding an integer. -/
lemma eK_add_intCast (x : ℝ) (k : ℤ) : eK (x + (k : ℝ)) = eK x := by
  have h : (((2 * π * (x + (k : ℝ))) : ℝ) : ℂ) * Complex.I
      = (((2 * π * x : ℝ)) : ℂ) * Complex.I + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast; ring
  simp only [eK, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `eK` in real cos/sin form. -/
lemma eK_eq (s : ℝ) :
    eK s = (Real.cos (2 * π * s) : ℂ) + (Real.sin (2 * π * s) : ℂ) * Complex.I := by
  simp only [eK, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

lemma eK_re (s : ℝ) : (eK s).re = Real.cos (2 * π * s) := by
  rw [eK_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

lemma eK_im (s : ℝ) : (eK s).im = Real.sin (2 * π * s) := by
  rw [eK_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

lemma one_sub_eK_re (s : ℝ) : (1 - eK s).re = 2 * Real.sin (π * s) ^ 2 := by
  have h1 : (1 - eK s).re = 1 - Real.cos (2 * π * s) := by simp [eK_re]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

lemma one_sub_eK_im (s : ℝ) : (1 - eK s).im = -(2 * Real.sin (π * s) * Real.cos (π * s)) := by
  have h1 : (1 - eK s).im = -Real.sin (2 * π * s) := by simp [eK_im]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.sin_two_mul]

lemma normSq_one_sub_eK (s : ℝ) : Complex.normSq (1 - eK s) = 4 * Real.sin (π * s) ^ 2 := by
  rw [Complex.normSq_apply, one_sub_eK_re, one_sub_eK_im]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

/-- Norm of `1 - eK s` as `2|sin(πs)|`. -/
lemma norm_one_sub_eK (s : ℝ) : ‖1 - eK s‖ = 2 * |Real.sin (π * s)| := by
  rw [Complex.norm_def, normSq_one_sub_eK]
  rw [show (4 : ℝ) * Real.sin (π * s) ^ 2 = (2 * |Real.sin (π * s)|) ^ 2 by
        rw [mul_pow]; rw [sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

/-- The telescoping weight. -/
noncomputable def wK (s : ℝ) : ℂ := (1 - eK s)⁻¹

/-- `Re (wK s) = 1/2` (constant!) whenever `sin(πs) ≠ 0`. -/
lemma wK_re (s : ℝ) (hs : Real.sin (π * s) ≠ 0) : (wK s).re = 1 / 2 := by
  rw [wK, Complex.inv_re, normSq_one_sub_eK, one_sub_eK_re]
  have : Real.sin (π * s) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp
  ring

/-- `Im (wK s) = cos(πs)/(2 sin(πs)) = cot(πs)/2`. -/
lemma wK_im (s : ℝ) (hs : Real.sin (π * s) ≠ 0) :
    (wK s).im = Real.cos (π * s) / (2 * Real.sin (π * s)) := by
  rw [wK, Complex.inv_im, normSq_one_sub_eK, one_sub_eK_im]
  field_simp
  ring

/-- `‖wK s‖ = 1 / (2|sin(πs)|)`. -/
lemma norm_wK (s : ℝ) : ‖wK s‖ = 1 / (2 * |Real.sin (π * s)|) := by
  rw [wK, norm_inv, norm_one_sub_eK, inv_eq_one_div]

/-- `sin(πs) > 0` for `s ∈ (0,1)`. -/
lemma sin_pi_mul_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < Real.sin (π * s) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

/-- Jordan's inequality, symmetrised: `sin(πs) ≥ 2δ` for `s ∈ [δ, 1-δ]`, `δ ≤ 1/2`. -/
lemma sin_pi_mul_ge {δ s : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hs1 : δ ≤ s)
    (hs2 : s ≤ 1 - δ) : 2 * δ ≤ Real.sin (π * s) := by
  have hkey : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → 2 * t ≤ Real.sin (π * t) := by
    intro t ht0 ht1
    have hj := Real.mul_le_sin (x := π * t) (by positivity) (by nlinarith [Real.pi_pos])
    have hid : 2 / π * (π * t) = 2 * t := by field_simp
    linarith [hid ▸ hj]
  by_cases h : s ≤ 1 / 2
  · exact le_trans (by linarith) (hkey s (by linarith) h)
  · replace h := not_le.mp h
    have hsym : Real.sin (π * s) = Real.sin (π * (1 - s)) := by
      rw [show π * (1 - s) = π - π * s by ring, Real.sin_pi_sub]
    rw [hsym]
    exact le_trans (by linarith) (hkey (1 - s) (by linarith) (by linarith))

/-- Monotonicity of `Im (wK ·) = cot(π ·)/2`: antitone on `(0,1)`. -/
lemma wK_im_antitone {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ < 1) :
    Real.cos (π * s₂) / (2 * Real.sin (π * s₂))
      ≤ Real.cos (π * s₁) / (2 * Real.sin (π * s₁)) := by
  have hs1 : 0 < Real.sin (π * s₁) := sin_pi_mul_pos h1 (lt_of_le_of_lt h12 h2)
  have hs2 : 0 < Real.sin (π * s₂) := sin_pi_mul_pos (lt_of_lt_of_le h1 h12) h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsin : 0 ≤ Real.sin (π * s₂ - π * s₁) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos, mul_pos Real.pi_pos h1]
  rw [Real.sin_sub] at hsin
  nlinarith [hsin]

/-- A purely imaginary complex number has norm equal to `|Im|`. -/
lemma norm_eq_abs_im_of_re_eq_zero {z : ℂ} (h : z.re = 0) : ‖z‖ = |z.im| := by
  rw [Complex.norm_def, Complex.normSq_apply, h, zero_mul, zero_add, ← sq,
    Real.sqrt_sq_eq_abs]

/-- Abel summation over `range (N+1)`, telescoped form. -/
lemma abel_range (C B : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ range (N + 1), C k * (B k - B (k + 1))
      = C 0 * B 0 - C N * B (N + 1) + ∑ k ∈ range N, (C (k + 1) - C k) * B (k + 1) := by
  induction N with
  | zero => simp; ring
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- **The Kusmin–Landau inequality (discrete form).**

Let `g n := f (n+1) - f n` be the consecutive differences of a phase `f`.
If `g` is monotone (increasing) on `(a, b]` and stays in a single unit
interval bounded away from the integers, `g n ∈ [m + δ, m + 1 - δ]` with
`δ ∈ (0, 1/2]`, then the exponential sum obeys
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 1 / δ`.  The constant is absolute (`C = 1`).

See the file header for why the single-interval hypothesis is essential
(the `Int.fract`-only form is genuinely too weak). -/
theorem kusmin_landau {f : ℕ → ℝ} {a b : ℕ} {δ : ℝ} {m : ℤ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hg_lb : ∀ n, a < n → n ≤ b → (m : ℝ) + δ ≤ f (n + 1) - f n)
    (hg_ub : ∀ n, a < n → n ≤ b → f (n + 1) - f n ≤ (m : ℝ) + 1 - δ)
    (hmono : ∀ n, a < n → n < b → f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ 1 / δ := by
  rcases Nat.lt_or_ge a b with hab | hab
  · -- Main case `a < b`.
    set N : ℕ := b - a - 1 with hNdef
    have hbN : b = a + 1 + N := by omega
    -- reindex `Ioc a b` to `range (N+1)`
    have hIoc : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, Finset.sum_Ico_eq_sum_range, show b + 1 - (a + 1) = N + 1 by omega]
    -- local sequences
    set σ : ℕ → ℝ := fun k => f (a + 1 + k + 1) - f (a + 1 + k) - (m : ℝ) with hσdef
    set B : ℕ → ℂ := fun k => eK (f (a + 1 + k)) with hBdef
    set W : ℕ → ℂ := fun k => wK (σ k) with hWdef
    -- range facts on `σ`
    have hσ_range : ∀ k, k ≤ N → δ ≤ σ k ∧ σ k ≤ 1 - δ := by
      intro k hk
      have h1 : a < a + 1 + k := by omega
      have h2 : a + 1 + k ≤ b := by omega
      have hlb := hg_lb (a + 1 + k) h1 h2
      have hub := hg_ub (a + 1 + k) h1 h2
      simp only [hσdef]; constructor <;> [linarith; linarith]
    have hsin_pos : ∀ k, k ≤ N → 0 < Real.sin (π * σ k) := by
      intro k hk
      obtain ⟨hl, hu⟩ := hσ_range k hk
      exact sin_pi_mul_pos (by linarith) (by linarith)
    have hsin_ge : ∀ k, k ≤ N → 2 * δ ≤ Real.sin (π * σ k) := by
      intro k hk
      obtain ⟨hl, hu⟩ := hσ_range k hk
      exact sin_pi_mul_ge hδ0 hδ hl hu
    have hσ_mono : ∀ k, k < N → σ k ≤ σ (k + 1) := by
      intro k hk
      have h1 : a < a + 1 + k := by omega
      have h2 : a + 1 + k < b := by omega
      have := hmono (a + 1 + k) h1 h2
      simp only [hσdef]
      have he : a + 1 + (k + 1) = a + 1 + k + 1 := by ring
      have he2 : a + 1 + k + 1 + 1 = a + 1 + k + 2 := by ring
      rw [he, he2]; linarith
    -- `Re W = 1/2`, `Im W = cot/2`, monotone, norm-bounded
    have hWre : ∀ k, k ≤ N → (W k).re = 1 / 2 := by
      intro k hk; simp only [hWdef]; exact wK_re _ (ne_of_gt (hsin_pos k hk))
    have hWim : ∀ k, k ≤ N →
        (W k).im = Real.cos (π * σ k) / (2 * Real.sin (π * σ k)) := by
      intro k hk; simp only [hWdef]; exact wK_im _ (ne_of_gt (hsin_pos k hk))
    have hWmono : ∀ k, k < N → (W (k + 1)).im ≤ (W k).im := by
      intro k hk
      rw [hWim (k + 1) (by omega), hWim k (by omega)]
      obtain ⟨hl, _⟩ := hσ_range k (by omega)
      obtain ⟨_, hu⟩ := hσ_range (k + 1) (by omega)
      exact wK_im_antitone (by linarith) (hσ_mono k hk) (by linarith)
    have hWimabs : ∀ k, k ≤ N → |(W k).im| ≤ 1 / (4 * δ) := by
      intro k hk
      have hs := hsin_pos k hk
      have hsg := hsin_ge k hk
      rw [hWim k hk, abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hs) (by positivity)]
      have hcos : |Real.cos (π * σ k)| ≤ 1 := Real.abs_cos_le_one _
      nlinarith [hcos, hsg, hδ0,
        mul_le_mul_of_nonneg_right hcos (by positivity : (0 : ℝ) ≤ 4 * δ)]
    have hWnorm : ∀ k, k ≤ N → ‖W k‖ ≤ 1 / (4 * δ) := by
      intro k hk
      simp only [hWdef, norm_wK]
      have hs := hsin_pos k hk
      have hsg := hsin_ge k hk
      rw [abs_of_pos hs]
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    -- pointwise Kusmin–Landau identity
    have hid : ∀ k, k ≤ N → W k * (B k - B (k + 1)) = B k := by
      intro k hk
      have hne : 1 - eK (σ k) ≠ 0 := by
        intro hzero
        rw [← norm_eq_zero, norm_one_sub_eK] at hzero
        have hs := hsin_pos k hk
        have : |Real.sin (π * σ k)| = 0 := by linarith [abs_nonneg (Real.sin (π * σ k))]
        rw [abs_eq_zero] at this; linarith
      have hBrec : B (k + 1) = B k * eK (σ k) := by
        simp only [hBdef]
        rw [show f (a + 1 + (k + 1)) = f (a + 1 + k) + (σ k + (m : ℝ)) by
              simp only [hσdef]; ring]
        rw [eK_add, eK_add_intCast]
      rw [hBrec]
      have hfac : B k - B k * eK (σ k) = B k * (1 - eK (σ k)) := by ring
      rw [hfac]
      simp only [hWdef, wK]
      rw [mul_comm (B k) (1 - eK (σ k)), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    -- Abel + triangle inequality
    have hsumeq : ∑ k ∈ Finset.range (N + 1), B k
        = ∑ k ∈ Finset.range (N + 1), W k * (B k - B (k + 1)) :=
      Finset.sum_congr rfl fun k hk => (hid k (by simpa using Finset.mem_range.mp hk)).symm
    have hBnorm : ∀ k, ‖B k‖ = 1 := fun k => by simp only [hBdef]; exact eK_norm _
    rw [hsumeq, abel_range W B N]
    -- variation telescopes to `Im (W 0) - Im (W N)`
    have hvar : ∀ k, k < N → ‖W (k + 1) - W k‖ = (W k).im - (W (k + 1)).im := by
      intro k hk
      have hre : (W (k + 1) - W k).re = 0 := by
        rw [Complex.sub_re, hWre (k + 1) (by omega), hWre k (by omega)]; ring
      rw [norm_eq_abs_im_of_re_eq_zero hre, Complex.sub_im,
        abs_of_nonpos (by linarith [hWmono k hk])]; ring
    have hvarsum : ∑ k ∈ Finset.range N, ‖W (k + 1) - W k‖ = (W 0).im - (W N).im := by
      rw [Finset.sum_congr rfl fun k hk => hvar k (Finset.mem_range.mp hk)]
      exact Finset.sum_range_sub' (fun k => (W k).im) N
    calc ‖W 0 * B 0 - W N * B (N + 1)
              + ∑ k ∈ Finset.range N, (W (k + 1) - W k) * B (k + 1)‖
        ≤ ‖W 0 * B 0 - W N * B (N + 1)‖
            + ‖∑ k ∈ Finset.range N, (W (k + 1) - W k) * B (k + 1)‖ := norm_add_le _ _
      _ ≤ (‖W 0 * B 0‖ + ‖W N * B (N + 1)‖)
            + ∑ k ∈ Finset.range N, ‖(W (k + 1) - W k) * B (k + 1)‖ := by
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sum_le _ _
      _ = (‖W 0‖ + ‖W N‖) + ∑ k ∈ Finset.range N, ‖W (k + 1) - W k‖ := by
          simp only [norm_mul, hBnorm, mul_one]
      _ = (‖W 0‖ + ‖W N‖) + ((W 0).im - (W N).im) := by rw [hvarsum]
      _ ≤ (1 / (4 * δ) + 1 / (4 * δ)) + (1 / (4 * δ) + 1 / (4 * δ)) := by
          gcongr
          · exact hWnorm 0 (by omega)
          · exact hWnorm N (by omega)
          · have h0 := le_trans (le_abs_self (W 0).im) (hWimabs 0 (by omega))
            have hN := le_trans (neg_le_abs (W N).im) (hWimabs N (by omega))
            linarith
      _ = 1 / δ := by field_simp; ring
  · -- Empty case `b ≤ a`.
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity

/-!
## Milestone 2 — the second-derivative test (RESIDUAL; paper arithmetic recorded)

**Target statement.**  With `g n := f (n+1) - f n`, additionally assume the
second differences obey `λ ≤ g (n+1) - g n ≤ c · λ` for all `n` in range
(`0 < λ`, `1 ≤ c`).  Then, with `L := (b : ℝ) - a`,
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 5 · (c · L · √λ + 1 / √λ)`   (absolute `C' = 5`).

**Paper arithmetic (fully worked; this is the deliverable design).**

Set `δ := √λ`.  Split on the size of `λ`:

* **Case `λ > 1/4`** (so `√λ > 1/2`).  Bound trivially:
  `‖S‖ ≤ #(Ioc a b) = L` (each `‖eK‖ = 1`).  Since `c ≥ 1` and `√λ > 1/2`,
  `L < 2·c·L·√λ ≤ 5·(c L √λ + 1/√λ)`.  ✔

* **Case `λ ≤ 1/4`** (so `δ = √λ ≤ 1/2`, and `λ ≤ 1`).  Because
  `g (n+1) - g n ≥ λ > 0`, `g` is *strictly increasing*.  Decompose
  `Ioc a b` fibrewise by `k := ⌊g n⌋` (`Finset.sum_fiberwise_of_maps_to`):
  each fibre `F_k := {n ∈ Ioc a b : ⌊g n⌋ = k}` is contiguous (`g` mono) and
  the fibres partition the range.  Within `F_k` split by monotonicity into

    - the **good part** `G_k := {n ∈ F_k : g n ∈ [k+δ, k+1-δ]}` — a single
      sub-`Ioc`, so `kusmin_landau` (with this `m := k`) gives
      `‖∑_{G_k} eK (f n)‖ ≤ 1/δ`;
    - the **bad part** `B_k := F_k \ G_k` = `{g n ∈ [k,k+δ) ∪ (k+1-δ,k+1)}`.
      Bound trivially by `#B_k`.  Since `g` increases by `≥ λ` per step, a
      window of `g`-length `w` holds `≤ w/λ + 1` indices, so each of the two
      bad sub-windows (length `δ`) has `≤ δ/λ + 1` indices:
      `#B_k ≤ 2·(δ/λ) + 2`.

  Number of non-empty fibres:
  `K ≤ ⌊g_b⌋ - ⌊g_{a+1}⌋ + 1 ≤ (g_b - g_{a+1}) + 1 ≤ c·λ·L + 1`.

  Summing over the `K` fibres:
  `‖S‖ ≤ K·(1/δ) + K·(2δ/λ + 2) = K·(1/δ + 2δ/λ + 2)`.
  With `δ = √λ`:  `1/δ = 1/√λ`, `2δ/λ = 2/√λ`, so the bracket is
  `3/√λ + 2`, and
  `‖S‖ ≤ (c λ L + 1)·(3/√λ + 2)`
       `= 3 c L √λ + 2 c λ L + 3/√λ + 2`.
  Using `λ ≤ 1` (`⇒ √λ ≤ 1`):  `2 c λ L = 2√λ·(c L √λ) ≤ 2 c L √λ` and
  `2 = 2√λ/√λ ≤ 2/√λ`.  Hence
  `‖S‖ ≤ 5 c L √λ + 5/√λ = 5·(c L √λ + 1/√λ)`.  ✔

Both cases give `C' = 5`.

**Why this is deferred (the real Lean cost).**  The elementary content above
needs three pieces of `Finset` engineering, the middle one being a genuine
sub-obstacle with no mathlib shortcut (see the recon: only the *identity*
predicate has `filter_lt_le_eq_Ioc`):

1.  fibrewise decomposition — available (`Finset.sum_fiberwise_of_maps_to`);
2.  **`G_k` (a monotone-predicate filter of an interval) equals an explicit
    `Finset.Ioc`** — must be built from `StrictMono (g)` by hand; this is a
    C-tier node in its own right and gates the `kusmin_landau` application;
3.  the crossing/window count `#B_k ≤ 2δ/λ + 2` and `K ≤ cλL + 1` from the
    per-step lower bound `g (n+1) - g n ≥ λ`.

`kusmin_landau` (milestone 1) is stated exactly to receive the good windows
`G_k` (single interval `m := k`, `g` increasing), so wiring is mechanical once
(2) lands.  Recorded as the named residual `VK-N2-M2` in `flags.md`.
-/

end Salt.ExpSum

end

-- ===== Salt.ExpSum.VdCorput2 =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# van der Corput's second-derivative test (Milestone 2)

This file discharges the `VK-N2-M2` residual: the discrete second-derivative
test built on top of `kusmin_landau` (Milestone 1, `Salt/ExpSum/Kusmin.lean`).

With `g n := f (n+1) - f n` the consecutive differences, if the second
differences satisfy `lam ≤ g (n+1) - g n ≤ c · lam` on the range (`0 < lam`,
`1 ≤ c`), then for `L := (b : ℝ) - a`,
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 8 · (c · L · √lam + 1 / √lam)`.

See the file `Kusmin.lean`'s Milestone-2 docstring for the full paper
arithmetic.  The engine here:

* `step_accum` — accumulate a per-step difference bound `g (n+1) - g n ≤ β`
  into `g q - g p ≤ (q - p) · β`.  Used twice (with `β = c·lam` and, via `-g`,
  with the lower bound `lam`).
* `fibre_is_interval` — **the sub-obstacle**: a `g`-monotone-predicate filter of
  an interval `Ioc a b` is itself a `Finset.Ioc`.  Built by hand from strict
  monotonicity via `min'`/`max'` (no mathlib shortcut exists for a general
  monotone predicate).  This is what lets each good window feed `kusmin_landau`.
* `count_window` — a window of `g`-length `w` holds `≤ w/lam + 1` indices, since
  `g` steps up by `≥ lam`.  Bounds the two bad windows per fibre.

**Constant.**  The recorded arithmetic advertised `C' = 5` using the (in general
false) step `⌊x⌋ - ⌊y⌋ ≤ x - y`; the honest fibre count is `K ≤ c·lam·L + 2`,
which lands the constant at `C' = 8` (explicitly permitted by the task).
-/

namespace Salt.ExpSum

open Real Finset

/-- **Step accumulation.**  If `g (n+1) - g n ≤ β` for every `n` strictly inside
`(a, b)`, then `g q - g p ≤ (q - p) · β` for `a < p ≤ q ≤ b`. -/
lemma step_accum {g : ℕ → ℝ} {a b : ℕ} {β : ℝ}
    (hstep : ∀ n, a < n → n < b → g (n + 1) - g n ≤ β)
    (p : ℕ) (hp : a < p) :
    ∀ q, p ≤ q → q ≤ b → g q - g p ≤ ((q : ℝ) - p) * β := by
  intro q hpq
  induction q, hpq using Nat.le_induction with
  | base => intro _; simp
  | succ q hpq ih =>
      intro hqb
      have h1 := ih (by omega)
      have h2 := hstep q (by omega) (by omega)
      have hexp : ((q + 1 : ℕ) : ℝ) - p = ((q : ℝ) - p) + 1 := by push_cast; ring
      rw [hexp, add_mul, one_mul]
      linarith

/-- **The fibre-is-an-interval lemma (the sub-obstacle).**  For a `g` strictly
monotone on `(a, b]` and reals `u ≤ v` (or any `u v`), the filter of `Ioc a b`
by the monotone predicate `u ≤ g n ∧ g n ≤ v` is a `Finset.Ioc a' b'` with
`a ≤ a'` and `b' ≤ b` (empty when `b' ≤ a'`). -/
lemma fibre_is_interval {g : ℕ → ℝ} {a b : ℕ}
    (hmono : ∀ p q, a < p → p < q → q ≤ b → g p < g q) (u v : ℝ) :
    ∃ a' b' : ℕ, a ≤ a' ∧ b' ≤ b ∧
      (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n ≤ v) = Finset.Ioc a' b' := by
  set T := (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n ≤ v) with hTdef
  rcases T.eq_empty_or_nonempty with he | hne
  · exact ⟨a, 0, le_refl a, Nat.zero_le b, by rw [he, Finset.Ioc_eq_empty (by omega)]⟩
  · have hn0mem : T.min' hne ∈ T := T.min'_mem hne
    have hn1mem : T.max' hne ∈ T := T.max'_mem hne
    set n0 := T.min' hne with hn0def
    set n1 := T.max' hne with hn1def
    obtain ⟨hn0Ioc, hn0lb, hn0ub⟩ := Finset.mem_filter.mp hn0mem
    obtain ⟨hn1Ioc, hn1lb, hn1ub⟩ := Finset.mem_filter.mp hn1mem
    obtain ⟨ha0, hb0⟩ := Finset.mem_Ioc.mp hn0Ioc
    obtain ⟨ha1, hb1⟩ := Finset.mem_Ioc.mp hn1Ioc
    refine ⟨n0 - 1, n1, by omega, hb1, ?_⟩
    ext x
    simp only [Finset.mem_Ioc]
    constructor
    · intro hx
      have hx0 : n0 ≤ x := Finset.min'_le T x hx
      have hx1 : x ≤ n1 := Finset.le_max' T x hx
      omega
    · rintro ⟨hlt, hle⟩
      have hx0 : n0 ≤ x := by omega
      have hxa : a < x := by omega
      have hxb : x ≤ b := le_trans hle hb1
      have hgx_lb : u ≤ g x := by
        rcases eq_or_lt_of_le hx0 with h | h
        · rw [← h]; exact hn0lb
        · exact le_trans hn0lb (le_of_lt (hmono n0 x ha0 h hxb))
      have hgx_ub : g x ≤ v := by
        rcases eq_or_lt_of_le hle with h | h
        · rw [h]; exact hn1ub
        · exact le_trans (le_of_lt (hmono x n1 hxa h hb1)) hn1ub
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hxa, hxb⟩, hgx_lb, hgx_ub⟩

/-- **Window count.**  If `g` steps up by `≥ lam > 0` (encoded via the lower
accumulation `hacc`), a window `[u, u+w)` of `g`-values holds at most
`w / lam + 1` indices in `Ioc a b`. -/
lemma count_window {g : ℕ → ℝ} {a b : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hacc : ∀ p q, a < p → p ≤ q → q ≤ b → ((q : ℝ) - p) * lam ≤ g q - g p)
    (u w : ℝ) (hw : 0 ≤ w) :
    (((Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n < u + w)).card : ℝ)
      ≤ w / lam + 1 := by
  set T := (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n < u + w) with hTdef
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ w / lam := div_nonneg hw (le_of_lt hlam)
    linarith
  · have hn0mem : T.min' hne ∈ T := T.min'_mem hne
    have hn1mem : T.max' hne ∈ T := T.max'_mem hne
    set n0 := T.min' hne with hn0def
    set n1 := T.max' hne with hn1def
    obtain ⟨hn0Ioc, hn0lb, hn0ub⟩ := Finset.mem_filter.mp hn0mem
    obtain ⟨hn1Ioc, hn1lb, hn1ub⟩ := Finset.mem_filter.mp hn1mem
    obtain ⟨ha0, hb0⟩ := Finset.mem_Ioc.mp hn0Ioc
    obtain ⟨ha1, hb1⟩ := Finset.mem_Ioc.mp hn1Ioc
    have hn01 : n0 ≤ n1 := T.min'_le_max' hne
    have hsub : T ⊆ Finset.Icc n0 n1 := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le T x hx, Finset.le_max' T x hx⟩
    have hcard : T.card ≤ (Finset.Icc n0 n1).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcardR : (T.card : ℝ) ≤ (n1 : ℝ) - n0 + 1 := by
      calc (T.card : ℝ) ≤ ((n1 + 1 - n0 : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (n1 : ℝ) - n0 + 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hspread : ((n1 : ℝ) - n0) * lam ≤ g n1 - g n0 := hacc n0 n1 ha0 hn01 hb1
    have hgdiff : g n1 - g n0 < w := by linarith
    have hn1n0 : (n1 : ℝ) - n0 ≤ w / lam := by
      rw [le_div_iff₀ hlam]; linarith
    linarith

/-- **van der Corput's second-derivative test (Milestone 2).**

With `g n := f (n+1) - f n`, if the second differences satisfy
`lam ≤ g (n+1) - g n ≤ c · lam` for all `a < n < b` (`0 < lam`, `1 ≤ c`), then
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 8 · (c · (b - a) · √lam + 1 / √lam)`.

The absolute constant is `C' = 8` (the recorded arithmetic advertised `5` using
a step that is false in general; see the header). -/
theorem vdC_second_derivative {f : ℕ → ℝ} {a b : ℕ} {lam c : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hc : 1 ≤ c)
    (h2nd_lb : ∀ n, a < n → n < b →
        lam ≤ (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n))
    (h2nd_ub : ∀ n, a < n → n < b →
        (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n) ≤ c * lam) :
    ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
      ≤ 8 * (c * ((b : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  set g : ℕ → ℝ := fun n => f (n + 1) - f n with hgdef
  set δ := Real.sqrt lam with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr hlam
  have hne : δ ≠ 0 := ne_of_gt hδpos
  -- step bounds in terms of g
  have hstep_lb : ∀ n, a < n → n < b → lam ≤ g (n + 1) - g n := by
    intro n h1 h2; have := h2nd_lb n h1 h2; simpa only [hgdef] using this
  have hstep_ub : ∀ n, a < n → n < b → g (n + 1) - g n ≤ c * lam := by
    intro n h1 h2; have := h2nd_ub n h1 h2; simpa only [hgdef] using this
  -- accumulations
  have hacc_hi : ∀ p q, a < p → p ≤ q → q ≤ b → g q - g p ≤ ((q : ℝ) - p) * (c * lam) := by
    intro p q hp hpq hqb; exact step_accum hstep_ub p hp q hpq hqb
  have hacc_lo : ∀ p q, a < p → p ≤ q → q ≤ b → ((q : ℝ) - p) * lam ≤ g q - g p := by
    intro p q hp hpq hqb
    have hstep' : ∀ n, a < n → n < b → (fun m => -g m) (n + 1) - (fun m => -g m) n ≤ -lam := by
      intro n hn1 hn2; dsimp only; linarith [hstep_lb n hn1 hn2]
    have key : -g q - -g p ≤ ((q : ℝ) - p) * (-lam) :=
      step_accum (g := fun m => -g m) hstep' p hp q hpq hqb
    rw [mul_neg] at key; linarith
  have hstrictmono : ∀ p q, a < p → p < q → q ≤ b → g p < g q := by
    intro p q hp hpq hqb
    have h := hacc_lo p q hp (le_of_lt hpq) hqb
    have hpos : (0 : ℝ) < ((q : ℝ) - p) * lam := by
      apply mul_pos _ hlam
      have : (p : ℝ) < q := by exact_mod_cast hpq
      linarith
    linarith
  by_cases hsmall : lam ≤ 1 / 4
  · -- ═══ main case: lam ≤ 1/4 (δ ≤ 1/2) ═══
    have hδhalf : δ ≤ 1 / 2 := by
      rw [hδdef, show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hsmall
    have hδsq : lam = δ ^ 2 := by rw [hδdef]; exact (Real.sq_sqrt (le_of_lt hlam)).symm
    have hδlam : δ / lam = 1 / δ := by rw [hδsq, sq]; field_simp
    rcases eq_or_lt_of_le hab with hEq | haltb
    · -- empty: a = b
      have hEq2 : b = a := hEq.symm
      subst hEq2
      rw [Finset.Ioc_self, Finset.sum_empty, norm_zero]
      simp only [sub_self, mul_zero, zero_mul, zero_add]
      positivity
    · -- a < b
      have hLpos : (0 : ℝ) < (b : ℝ) - a := by
        have : (a : ℝ) < b := by exact_mod_cast haltb
        linarith
      have hLnn : (0 : ℝ) ≤ (b : ℝ) - a := le_of_lt hLpos
      set φ : ℕ → ℤ := fun n => ⌊g n⌋ with hφdef
      set K := (Finset.Ioc a b).image φ with hKdef
      have hmaps : ∀ n ∈ Finset.Ioc a b, φ n ∈ K := fun n hn => Finset.mem_image_of_mem φ hn
      -- STEP 1: triangle over fibres
      have hStep1 : ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => eK (f n))]
        exact norm_sum_le _ _
      -- PER-FIBRE bound
      have hfibre : ∀ k ∈ K,
          ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ ≤ 3 / δ + 2 := by
        intro k _
        set Fk := (Finset.Ioc a b).filter (fun n => φ n = k) with hFkdef
        set Gk := (Finset.Ioc a b).filter
          (fun n => (k : ℝ) + δ ≤ g n ∧ g n ≤ (k : ℝ) + 1 - δ) with hGkdef
        have hGsub : Gk ⊆ Fk := by
          intro n hn
          rw [hGkdef, Finset.mem_filter] at hn
          obtain ⟨hnIoc, hlb, hub⟩ := hn
          rw [hFkdef, Finset.mem_filter]
          refine ⟨hnIoc, ?_⟩
          rw [hφdef]
          exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
        have hsplit : ∑ n ∈ Fk, eK (f n)
            = (∑ n ∈ Fk \ Gk, eK (f n)) + (∑ n ∈ Gk, eK (f n)) :=
          (Finset.sum_sdiff hGsub).symm
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        -- good part via kusmin
        have hgood : ‖∑ n ∈ Gk, eK (f n)‖ ≤ 1 / δ := by
          obtain ⟨a', b', ha', hb', hGeq⟩ :=
            fibre_is_interval hstrictmono ((k : ℝ) + δ) ((k : ℝ) + 1 - δ)
          have hGkeq : Gk = Finset.Ioc a' b' := by rw [hGkdef]; exact hGeq
          rw [hGkeq]
          apply kusmin_landau hδpos hδhalf
          · intro n hn1 hn2
            have hnmem : n ∈ Gk := by rw [hGkeq]; exact Finset.mem_Ioc.mpr ⟨hn1, hn2⟩
            rw [hGkdef, Finset.mem_filter] at hnmem
            exact hnmem.2.1
          · intro n hn1 hn2
            have hnmem : n ∈ Gk := by rw [hGkeq]; exact Finset.mem_Ioc.mpr ⟨hn1, hn2⟩
            rw [hGkdef, Finset.mem_filter] at hnmem
            exact hnmem.2.2
          · intro n hn1 hn2
            exact le_of_lt (hstrictmono n (n + 1) (by omega) (by omega) (by omega))
        -- bad part via count_window
        have hbad : ‖∑ n ∈ Fk \ Gk, eK (f n)‖ ≤ 2 / δ + 2 := by
          have hcardbound : ((Fk \ Gk).card : ℝ) ≤ 2 / δ + 2 := by
            set Left := (Finset.Ioc a b).filter
              (fun n => (k : ℝ) ≤ g n ∧ g n < (k : ℝ) + δ) with hLeftdef
            set Right := (Finset.Ioc a b).filter
              (fun n => (k : ℝ) + 1 - δ ≤ g n ∧ g n < (k : ℝ) + 1 - δ + δ) with hRightdef
            have hsubLR : Fk \ Gk ⊆ Left ∪ Right := by
              intro n hn
              rw [Finset.mem_sdiff] at hn
              obtain ⟨hnFk, hnGk⟩ := hn
              rw [hFkdef, Finset.mem_filter] at hnFk
              obtain ⟨hnIoc, hφk⟩ := hnFk
              rw [hφdef] at hφk
              obtain ⟨hgk1, hgk2⟩ := Int.floor_eq_iff.mp hφk
              rw [hGkdef, Finset.mem_filter, not_and] at hnGk
              have hnotpred := hnGk hnIoc
              rw [not_and_or] at hnotpred
              rw [Finset.mem_union]
              rcases hnotpred with h | h
              · left
                rw [hLeftdef, Finset.mem_filter]
                rw [not_le] at h
                exact ⟨hnIoc, hgk1, h⟩
              · right
                rw [hRightdef, Finset.mem_filter]
                rw [not_le] at h
                refine ⟨hnIoc, le_of_lt h, ?_⟩
                have he : (k : ℝ) + 1 - δ + δ = (k : ℝ) + 1 := by ring
                rw [he]; exact hgk2
            have hcLR : (Fk \ Gk).card ≤ Left.card + Right.card :=
              le_trans (Finset.card_le_card hsubLR) (Finset.card_union_le Left Right)
            have hLeftC : (Left.card : ℝ) ≤ δ / lam + 1 :=
              count_window hlam hacc_lo (k : ℝ) δ (le_of_lt hδpos)
            have hRightC : (Right.card : ℝ) ≤ δ / lam + 1 :=
              count_window hlam hacc_lo ((k : ℝ) + 1 - δ) δ (le_of_lt hδpos)
            rw [hδlam] at hLeftC hRightC
            have hcast : ((Fk \ Gk).card : ℝ) ≤ (Left.card : ℝ) + (Right.card : ℝ) := by
              exact_mod_cast hcLR
            have hbridge : (2 : ℝ) / δ = 1 / δ + 1 / δ := by ring
            linarith [hcast, hLeftC, hRightC, hbridge]
          calc ‖∑ n ∈ Fk \ Gk, eK (f n)‖
              ≤ ∑ n ∈ Fk \ Gk, ‖eK (f n)‖ := norm_sum_le _ _
            _ = ∑ n ∈ Fk \ Gk, (1 : ℝ) := by simp [eK_norm]
            _ = ((Fk \ Gk).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ ≤ 2 / δ + 2 := hcardbound
        have hbridge : (3 : ℝ) / δ = 2 / δ + 1 / δ := by ring
        linarith [hgood, hbad, hbridge]
      -- STEP 2: sum the fibre bounds
      have hStep2 : ∑ k ∈ K,
          ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖
          ≤ (K.card : ℝ) * (3 / δ + 2) := by
        calc ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖
            ≤ ∑ _k ∈ K, (3 / δ + 2) := Finset.sum_le_sum hfibre
          _ = (K.card : ℝ) * (3 / δ + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      -- fibre count K ≤ c·lam·L + 2
      have hKcard : (K.card : ℝ) ≤ c * lam * ((b : ℝ) - a) + 2 := by
        have hφmono : ∀ n ∈ Finset.Ioc a b, φ (a + 1) ≤ φ n ∧ φ n ≤ φ b := by
          intro n hn
          obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
          simp only [hφdef]
          refine ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩
          · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hna) with h | h
            · exact le_of_eq (congrArg g h)
            · exact le_of_lt (hstrictmono (a + 1) n (by omega) h hnb)
          · rcases eq_or_lt_of_le hnb with h | h
            · exact le_of_eq (congrArg g h)
            · exact le_of_lt (hstrictmono n b hna h (le_refl b))
        have hKsub : K ⊆ Finset.Icc (φ (a + 1)) (φ b) := by
          intro z hz
          rw [hKdef, Finset.mem_image] at hz
          obtain ⟨n, hn, rfl⟩ := hz
          rw [Finset.mem_Icc]
          exact hφmono n hn
        have hmemA : a + 1 ∈ Finset.Ioc a b :=
          Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        have hφab : φ (a + 1) ≤ φ b := (hφmono (a + 1) hmemA).2
        have hcardZ : (K.card : ℤ) ≤ φ b + 1 - φ (a + 1) := by
          have h1 : K.card ≤ (Finset.Icc (φ (a + 1)) (φ b)).card := Finset.card_le_card hKsub
          have h2 : ((Finset.Icc (φ (a + 1)) (φ b)).card : ℤ) = φ b + 1 - φ (a + 1) := by
            rw [Int.card_Icc, Int.toNat_of_nonneg (show (0 : ℤ) ≤ φ b + 1 - φ (a + 1) by omega)]
          calc (K.card : ℤ) ≤ ((Finset.Icc (φ (a + 1)) (φ b)).card : ℤ) := by exact_mod_cast h1
            _ = φ b + 1 - φ (a + 1) := h2
        have hKR : (K.card : ℝ) ≤ (φ b : ℝ) + 1 - (φ (a + 1) : ℝ) := by
          calc (K.card : ℝ) = ((K.card : ℤ) : ℝ) := by push_cast; ring
            _ ≤ ((φ b + 1 - φ (a + 1) : ℤ) : ℝ) := by exact_mod_cast hcardZ
            _ = (φ b : ℝ) + 1 - (φ (a + 1) : ℝ) := by push_cast; ring
        have hfb : (φ b : ℝ) ≤ g b := by rw [hφdef]; exact Int.floor_le (g b)
        have hfa : g (a + 1) - 1 < (φ (a + 1) : ℝ) := by
          rw [hφdef]; exact Int.sub_one_lt_floor (g (a + 1))
        have hgub := hacc_hi (a + 1) b (by omega) (by omega) (le_refl b)
        have hclam : (0 : ℝ) ≤ c * lam := mul_nonneg (by linarith) (le_of_lt hlam)
        have hgub2 : g b - g (a + 1) ≤ c * lam * ((b : ℝ) - a) := by
          have hstep : ((b : ℝ) - (a + 1)) * (c * lam) ≤ c * lam * ((b : ℝ) - a) := by
            nlinarith [hclam]
          push_cast at hgub
          linarith [hgub, hstep]
        linarith [hKR, hfb, hfa, hgub2]
      -- FINAL arithmetic
      have hfinal : (K.card : ℝ) * (3 / δ + 2) ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := by
        have hcleared : (c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)
            ≤ 8 * (c * ((b : ℝ) - a) * δ) * δ + 8 := by
          rw [hδsq]
          nlinarith [hδpos, hδhalf, hLnn, hc,
            mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c) hLnn) (sq_nonneg δ),
            mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c) hLnn)
              (sq_nonneg δ)) (by linarith : (0 : ℝ) ≤ 5 - 2 * δ)]
        have e1 : (c * lam * ((b : ℝ) - a) + 2) * (3 / δ + 2)
            = ((c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)) / δ := by field_simp
        have e2 : 8 * (c * ((b : ℝ) - a) * δ + 1 / δ)
            = (8 * (c * ((b : ℝ) - a) * δ) * δ + 8) / δ := by field_simp
        calc (K.card : ℝ) * (3 / δ + 2)
            ≤ (c * lam * ((b : ℝ) - a) + 2) * (3 / δ + 2) :=
              mul_le_mul_of_nonneg_right hKcard (by positivity)
          _ = ((c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)) / δ := e1
          _ ≤ (8 * (c * ((b : ℝ) - a) * δ) * δ + 8) / δ :=
              (div_le_div_iff_of_pos_right hδpos).mpr hcleared
          _ = 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := e2.symm
      calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ := hStep1
        _ ≤ (K.card : ℝ) * (3 / δ + 2) := hStep2
        _ ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := hfinal
  · -- ═══ trivial case: lam > 1/4 (δ > 1/2) ═══
    have hbig : (1 : ℝ) / 4 < lam := not_le.mp hsmall
    have hδhalf : (1 : ℝ) / 2 < δ := by
      rw [hδdef, show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hbig
    have hL : (0 : ℝ) ≤ (b : ℝ) - a := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have hnorm : ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ (b : ℝ) - a := by
      calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ n ∈ Finset.Ioc a b, ‖eK (f n)‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.Ioc a b, (1 : ℝ) := by simp [eK_norm]
        _ = ((Finset.Ioc a b).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = (b : ℝ) - a := by rw [Nat.card_Ioc, Nat.cast_sub hab]
    have hcδ : (1 : ℝ) / 2 ≤ c * δ := by
      nlinarith [hc, hδhalf, hδpos, mul_nonneg (sub_nonneg.mpr hc) (le_of_lt hδpos)]
    have hbound : (b : ℝ) - a ≤ 8 * (c * ((b : ℝ) - a) * δ) := by
      nlinarith [hL, hcδ, mul_nonneg hL (by linarith [hcδ] : (0 : ℝ) ≤ c * δ - 1 / 2)]
    have h1δ : (0 : ℝ) ≤ 1 / δ := by positivity
    calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ (b : ℝ) - a := hnorm
      _ ≤ 8 * (c * ((b : ℝ) - a) * δ) := hbound
      _ ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := by linarith

end Salt.ExpSum

end




theorem solution {f : ℕ → ℝ} {a b : ℕ} {lam c : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hc : 1 ≤ c)
    (h2nd_lb : ∀ n, a < n → n < b →
        lam ≤ (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n))
    (h2nd_ub : ∀ n, a < n → n < b →
        (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n) ≤ c * lam) :
    ‖∑ n ∈ Finset.Ioc a b, Complex.exp (((2 * Real.pi * f n : ℝ) : ℂ) * Complex.I)‖
      ≤ 8 * (c * ((b : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) :=
  Salt.ExpSum.vdC_second_derivative hab hlam hc h2nd_lb h2nd_ub

