-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.lemma_1_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T00:51:20.674073+00:00
-- url     : https://prove2.me/submissions/2bd66ce6-79be-475d-8e81-efad837a6f5e

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity


open Filter Topology Asymptotics Set

namespace CohenPriceFairness.LocalWelfare.Proofs

theorem c1_deriv_est {f : ℝ → ℝ} {m a : ℝ} (hf : HasDerivAt f m a) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ > 0, ∀ X, |X| < δ → |f (a + X) - f a - X * m| ≤ κ * |X| := by
  have h := (hasDerivAt_iff_isLittleO_nhds_zero.mp hf).def hκ
  rcases Metric.eventually_nhds_iff.mp h with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have := hball (y := X) (by simpa [Real.dist_eq] using hX)
  simpa [Real.norm_eq_abs, smul_eq_mul] using this

theorem c1_core (f g : ℝ → ℝ) (a c m n u w : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hcont : ∃ η > 0, ContinuousOn f (Icc (a - η) (a + η)))
    (hf : HasDerivAt f m a) (hg : HasDerivAt g n c) (hm : m ≠ 0)
    (hv : m * u + n * w = -(f a + g c)) :
    ∀ τ > 0, ∃ ε > 0, ∀ α ∈ Ioc (0 : ℝ) ε, ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧
      |f x + g y| ≤ (1 - α) * |f a + g c| ∧ |x - a - α * u| ≤ τ * α ∧
      |y - c - α * w| ≤ τ * α := by
  intro τ hτ
  obtain ⟨η, hη, hfc⟩ := hcont
  set L := |u| + |w| + τ + 1 with hL
  have hLpos : 0 < L := by positivity
  have hm' : 0 < |m| := abs_pos.mpr hm
  set κ := |m| * τ / (2 * L) with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨δ1, hδ1, e1⟩ := c1_deriv_est hf hκ
  obtain ⟨δ2, hδ2, e2⟩ := c1_deriv_est hg hκ
  refine ⟨min 1 (min (δ1 / (2 * L)) (min (δ2 / (2 * L)) (min (η / L) (min (a / L) (c / L))))),
    by positivity, ?_⟩
  rintro α ⟨hα0, hαε⟩
  simp only [le_min_iff] at hαε
  obtain ⟨hα1, hαd1, hαd2, hαη, hαa, hαc⟩ := hαε
  rw [le_div_iff₀ (by positivity)] at hαd1 hαd2
  rw [le_div_iff₀ hLpos] at hαη hαa hαc
  have hu : |u| ≤ L := by rw [hL]; linarith [abs_nonneg w]
  have hw : |w| ≤ L := by rw [hL]; linarith [abs_nonneg u]
  have hut : |u| + τ ≤ L := by rw [hL]; linarith [abs_nonneg w]
  have hαut := mul_le_mul_of_nonneg_left hut hα0.le
  have hαw := mul_le_mul_of_nonneg_left hw hα0.le
  set s := τ * α with hs
  have hs0 : 0 < s := by positivity
  set Δ := f a + g c with hΔ
  let h : ℝ → ℝ := fun t => f (a + α * u + t) + g (c + α * w) - (1 - α) * Δ
  -- key expansion
  have hY : |α * w| < δ2 := by
    rw [abs_mul, abs_of_pos hα0]
    nlinarith [mul_le_mul_of_nonneg_left hw hα0.le]
  have E2 := e2 (α * w) hY
  have key : ∀ t, |t| ≤ s → |h t - m * t| ≤ κ * α * (|u| + τ + |w|) := by
    intro t ht
    have hX : |α * u + t| < δ1 := by
      calc |α * u + t| ≤ |α * u| + |t| := abs_add_le _ _
        _ ≤ α * L := by
          rw [abs_mul, abs_of_pos hα0]
          nlinarith [mul_le_mul_of_nonneg_left hut hα0.le]
        _ < δ1 := by nlinarith
    have E1 := e1 (α * u + t) hX
    have : h t - m * t = (f (a + (α * u + t)) - f a - (α * u + t) * m)
        + (g (c + α * w) - g c - α * w * n) := by
      simp only [h, ← add_assoc]
      have : α * Δ = - (α * (m * u + n * w)) := by rw [hv]; ring
      linear_combination this
    rw [this]
    have hXb : |α * u + t| ≤ α * |u| + α * τ := by
      calc |α * u + t| ≤ |α * u| + |t| := abs_add_le _ _
        _ ≤ α * |u| + α * τ := by rw [abs_mul, abs_of_pos hα0]; linarith
    have hYb : |α * w| = α * |w| := by rw [abs_mul, abs_of_pos hα0]
    calc _ ≤ |f (a + (α * u + t)) - f a - (α * u + t) * m| + |g (c + α * w) - g c - α * w * n| :=
          abs_add_le _ _
      _ ≤ κ * |α * u + t| + κ * |α * w| := add_le_add E1 E2
      _ ≤ κ * (α * |u| + α * τ) + κ * (α * |w|) := by
          rw [hYb]; gcongr
      _ = κ * α * (|u| + τ + |w|) := by ring
  have hbound : κ * α * (|u| + τ + |w|) < |m| * s := by
    have h1 : κ * (|u| + τ + |w|) < |m| * τ := by
      rw [hκdef]
      have : |u| + τ + |w| < 2 * L := by rw [hL]; linarith [abs_nonneg u, abs_nonneg w]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hm' hτ]
    rw [hs]; nlinarith
  -- continuity of h on [-s, s]
  have hcont_h : ContinuousOn h (uIcc (-s) s) := by
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.add _ continuousOn_const
    apply hfc.comp (by fun_prop)
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hau := neg_abs_le u
    have hau' := le_abs_self u
    have h1 := mul_le_mul_of_nonneg_left hau hα0.le
    have h2 := mul_le_mul_of_nonneg_left hau' hα0.le
    constructor <;> nlinarith
  have hsign : (0 : ℝ) ∈ uIcc (h (-s)) (h s) := by
    have k1 := abs_le.mp (le_trans (key s (by rw [abs_of_pos hs0])) hbound.le)
    have k2 := abs_le.mp (le_trans (key (-s) (by rw [abs_neg, abs_of_pos hs0])) hbound.le)
    rw [mul_neg] at k2
    obtain ⟨k1a, k1b⟩ := k1
    obtain ⟨k2a, k2b⟩ := k2
    rw [mem_uIcc]
    rcases lt_or_gt_of_ne hm with hneg | hpos
    · rw [abs_of_neg hneg] at hbound k1a k1b k2a k2b
      right
      constructor <;> linarith
    · rw [abs_of_pos hpos] at hbound k1a k1b k2a k2b
      left
      constructor <;> linarith
  obtain ⟨t, ht, hht⟩ := intermediate_value_uIcc hcont_h hsign
  rw [uIcc_of_le (by linarith)] at ht
  obtain ⟨ht1, ht2⟩ := ht
  refine ⟨a + α * u + t, c + α * w, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left (neg_abs_le u) hα0.le
    have h3 : α * L ≤ a := hαa
    have h4 : α * (|u| + τ) = α * |u| + τ * α := by ring
    have h5 : α * -|u| = -(α * |u|) := by ring
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (neg_abs_le w) hα0.le
    have h5 : α * -|w| = -(α * |w|) := by ring
    have h6 : α * |w| ≤ α * L := hαw
    linarith
  · have : f (a + α * u + t) + g (c + α * w) = (1 - α) * Δ := by
      simp only [h] at hht; linarith
    rw [this, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - α)]
  · rw [show a + α * u + t - a - α * u = t by ring, abs_le]; constructor <;> linarith
  · rw [show c + α * w - c - α * w = 0 by ring, abs_zero]; positivity

theorem core_feasible_curve
    (M : Fin 2 → ℝ → ℝ) (b mm v : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hv : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1))) :
    ∀ τ > 0, ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε, ∃ q : Fin 2 → ℝ,
      (∀ i, 0 ≤ q i) ∧
      |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)| ∧
      ∀ i, |q i - b i - α * v i| ≤ τ * α := by
  intro τ hτ
  obtain ⟨η, hη, hc⟩ := hcont
  rcases hmm with h0 | h1
  · obtain ⟨ε, hε, H⟩ := c1_core (M 0) (fun y => -M 1 y) (b 0) (b 1) (mm 0) (-mm 1) (v 0) (v 1)
      (hb 0) (hb 1) ⟨η, hη, hc 0⟩ (hMd 0) (hMd 1).neg h0 (by linear_combination hv) τ hτ
    refine ⟨ε, hε, fun α hα => ?_⟩
    obtain ⟨x, y, hx, hy, hD, hxv, hyv⟩ := H α hα
    refine ⟨![x, y], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simpa
    · simpa [sub_eq_add_neg] using hD
    · intro i; fin_cases i <;> simpa
  · obtain ⟨ε, hε, H⟩ := c1_core (fun y => -M 1 y) (M 0) (b 1) (b 0) (-mm 1) (mm 0) (v 1) (v 0)
      (hb 1) (hb 0) ⟨η, hη, (hc 1).neg⟩ (hMd 1).neg (hMd 0) (neg_ne_zero.mpr h1)
      (by linear_combination hv) τ hτ
    refine ⟨ε, hε, fun α hα => ?_⟩
    obtain ⟨x, y, hx, hy, hD, hxv, hyv⟩ := H α hα
    refine ⟨![y, x], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simpa
    · have e1 : M 0 y - M 1 x = -M 1 x + M 0 y := by ring
      have e2 : M 0 (b 0) - M 1 (b 1) = -M 1 (b 1) + M 0 (b 0) := by ring
      simpa [e1, e2] using hD
    · intro i; fin_cases i <;> simpa

end CohenPriceFairness.LocalWelfare.Proofs




/-!
# C2 — `core_sensitivity` (the perturbation theorem)

Proof outline:
* `c2_lower`: along the first-order direction `v*` (via `core_feasible_curve`) there are feasible
  points with total profit `≥ R0(b0)+R1(b1) + (Σ r_i/2 v*_i^2 - κ) α^2`.
* `c2_exist`: existence of a constrained maximiser by compactness of a small box.
* `c2_core`: localisation, `P α - b = O(α)`, and the Lagrange identity give `(P α - b)/α → v*`,
  whence the welfare difference quotient converges.
-/

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Proofs

theorem c2_lin (f : ℝ → ℝ) (c x : ℝ) (hf : HasDerivAt f c x) (u : ℝ → ℝ)
    (hu : Tendsto u (𝓝[>] 0) (𝓝 x)) (hO : (fun α => u α - x) =O[𝓝[>] 0] (fun α => α)) :
    (fun α => f (u α) - f x - c * (u α - x)) =o[𝓝[>] 0] (fun α => α) := by
  have h1 := (hf.isLittleO.comp_tendsto hu).trans_isBigO hO
  refine h1.congr_left ?_
  intro α
  simp [Function.comp, smul_eq_mul, mul_comm]

theorem c2_sq_o : (fun α : ℝ => α ^ 2) =o[𝓝[>] 0] (fun α => α) :=
  (isLittleO_pow_id (by norm_num)).mono nhdsWithin_le_nhds

theorem c2_ev_small (C δ : ℝ) (hδ : 0 < δ) : ∀ᶠ α in 𝓝[>] (0:ℝ), C * α ^ 2 < δ := by
  have : Tendsto (fun α : ℝ => C * α ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun α : ℝ => C * α ^ 2) (𝓝 0) (𝓝 (C * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  exact this.eventually_lt_const hδ

theorem c2_exists_of_ev (p : ℝ → Prop) (h : ∀ᶠ α in 𝓝[>] (0:ℝ), p α) :
    ∃ ε > 0, ∀ α ∈ Set.Ioc (0:ℝ) ε, p α := by
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 h with ⟨u, hu, hsub⟩
  exact ⟨u, hu, fun α hα => hsub hα⟩

theorem c2_lower_i (Ri : ℝ → ℝ) (bi ri vi τ α ρ qi : ℝ) (hr : ri < 0) (hτ : 0 < τ) (hα : 0 < α)
    (hρ : ∀ y, |y| < ρ → |Ri (bi + y) - Ri bi - ri / 2 * y ^ 2| ≤ τ * y ^ 2)
    (hq : |qi - bi - α * vi| ≤ τ * α) (hαρ : α * (|vi| + τ) < ρ) :
    Ri bi + (ri / 2 - τ) * (|vi| + τ) ^ 2 * α ^ 2 ≤ Ri qi := by
  set y := qi - bi with hy
  have hyb : |y| ≤ α * (|vi| + τ) := by
    have h1 : |y| ≤ |y - α * vi| + |α * vi| := by
      have := abs_add_le (y - α * vi) (α * vi)
      simpa using this
    rw [abs_mul, abs_of_pos hα] at h1
    nlinarith
  have hy2 : y ^ 2 ≤ (α * (|vi| + τ)) ^ 2 := by
    have := abs_le.mp hyb
    exact sq_le_sq' this.1 this.2
  have h3 := hρ y (lt_of_le_of_lt hyb hαρ)
  have hq' : bi + y = qi := by rw [hy]; ring
  rw [hq'] at h3
  have h4 := (abs_le.mp h3).1
  have h5 : (ri / 2 - τ) * (α * (|vi| + τ)) ^ 2 ≤ (ri / 2 - τ) * y ^ 2 :=
    mul_le_mul_of_nonpos_left hy2 (by linarith)
  nlinarith

theorem c2_rho (R : ℝ → ℝ) (b r : ℝ)
    (hRt : (fun h => R (b + h) - R b - r / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ ρ > 0, ∀ y, |y| < ρ → |R (b + y) - R b - r / 2 * y ^ 2| ≤ τ * y ^ 2 := by
  have h := hRt.def hτ
  rcases Metric.eventually_nhds_iff.1 h with ⟨ρ, hρ, hh⟩
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  have := hh (y := y) (by simpa [Real.dist_eq] using hy)
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg y)] using this

theorem c2_lower (R M : Fin 2 → ℝ → ℝ) (b r mm v : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hcontM : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hv : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1))) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ α in 𝓝[>] (0:ℝ), ∃ q : Fin 2 → ℝ,
      ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      R 0 (b 0) + R 1 (b 1) + (r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 - κ) * α ^ 2 ≤
        R 0 (q 0) + R 1 (q 1) := by
  set g : ℝ → ℝ := fun τ => (r 0 / 2 - τ) * (|v 0| + τ) ^ 2 + (r 1 / 2 - τ) * (|v 1| + τ) ^ 2
    with hg
  have hgc : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := by
    have : Continuous g := by rw [hg]; fun_prop
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hg0 : g 0 = r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 := by
    simp [hg, sq_abs]
  have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 - κ < g τ ∧ 0 < τ := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    rw [← hg0]
    exact hgc.eventually_const_lt (by linarith)
  obtain ⟨τ, hτg, hτ⟩ := hev.exists
  obtain ⟨ρ0, hρ0, hρ0'⟩ := c2_rho (R 0) (b 0) (r 0) (hRt 0) τ hτ
  obtain ⟨ρ1, hρ1, hρ1'⟩ := c2_rho (R 1) (b 1) (r 1) (hRt 1) τ hτ
  obtain ⟨ε1, hε1, hcurve⟩ := core_feasible_curve M b mm v hb hcontM hMd hmm hv τ hτ
  have hsm : ∀ (c ρ : ℝ), 0 < ρ → ∀ᶠ α in 𝓝[>] (0:ℝ), α * c < ρ := by
    intro c ρ hρ
    have : Tendsto (fun α : ℝ => α * c) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun α : ℝ => α * c) (𝓝 0) (𝓝 (0 * c)) :=
        (continuous_id.mul continuous_const).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    exact this.eventually_lt_const hρ
  filter_upwards [Ioc_mem_nhdsGT hε1, hsm (|v 0| + τ) ρ0 hρ0, hsm (|v 1| + τ) ρ1 hρ1]
    with α hα h0 h1
  obtain ⟨q, hq0, hq1, hq2⟩ := hcurve α hα
  refine ⟨q, ⟨hq0, hq1⟩, ?_⟩
  have e0 := c2_lower_i (R 0) (b 0) (r 0) (v 0) τ α ρ0 (q 0) (hr 0) hτ hα.1 hρ0' (hq2 0) h0
  have e1 := c2_lower_i (R 1) (b 1) (r 1) (v 1) τ α ρ1 (q 1) (hr 1) hτ hα.1 hρ1' (hq2 1) h1
  have : (r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 - κ) * α ^ 2 ≤ g τ * α ^ 2 :=
    mul_le_mul_of_nonneg_right hτg.le (sq_nonneg α)
  simp only [hg] at this
  nlinarith

theorem c2_each (R : Fin 2 → ℝ → ℝ) (b : Fin 2 → ℝ)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i)) (q : Fin 2 → ℝ) (hq : ∀ i, 0 ≤ q i)
    (δ : ℝ) (h : R 0 (b 0) + R 1 (b 1) - δ ≤ R 0 (q 0) + R 1 (q 1)) :
    ∀ i, R i (b i) - δ ≤ R i (q i) := by
  have h0 := hopt 0 (q 0) (hq 0)
  have h1 := hopt 1 (q 1) (hq 1)
  intro i; fin_cases i <;> simp <;> linarith

theorem c2_exist (R M : Fin 2 → ℝ → ℝ) (b : Fin 2 → ℝ) (C : ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (R i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hq : ∀ᶠ α in 𝓝[>] (0:ℝ), ∃ q : Fin 2 → ℝ,
      ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      R 0 (b 0) + R 1 (b 1) + C * α ^ 2 ≤ R 0 (q 0) + R 1 (q 1)) :
    ∃ ε > 0, ∀ α ∈ Set.Icc (0 : ℝ) ε, ∃ p : Fin 2 → ℝ,
      ((∀ i, 0 ≤ p i) ∧ |M 0 (p 0) - M 1 (p 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      ∀ q : Fin 2 → ℝ,
        ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
        R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1) := by
  obtain ⟨η, hη, hc⟩ := hcont
  set ε0 := min η (min (b 0) (b 1)) / 2 with hε0d
  have hm1 : min η (min (b 0) (b 1)) ≤ η := min_le_left _ _
  have hm2 : min η (min (b 0) (b 1)) ≤ b 0 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm3 : min η (min (b 0) (b 1)) ≤ b 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hmpos : 0 < min η (min (b 0) (b 1)) := lt_min hη (lt_min (hb 0) (hb 1))
  have hε0 : 0 < ε0 := by rw [hε0d]; linarith
  have hε0η : ε0 < η := by rw [hε0d]; linarith
  have hε0b : ∀ i, ε0 < b i := by
    intro i; fin_cases i
    · simp; rw [hε0d]; linarith
    · simp; rw [hε0d]; linarith
  obtain ⟨δ0, hδ0, hl⟩ := hloc ε0 hε0
  obtain ⟨ε, hε, hall⟩ := c2_exists_of_ev _ (hq.and (c2_ev_small (-C) δ0 hδ0))
  refine ⟨ε, hε, fun α hα => ?_⟩
  rcases eq_or_lt_of_le hα.1 with h0 | hpos
  · subst h0
    refine ⟨b, ⟨fun i => (hb i).le, by simp⟩, fun q hq => ?_⟩
    have := hopt 0 (q 0) (hq.1 0)
    have := hopt 1 (q 1) (hq.1 1)
    linarith
  obtain ⟨⟨q, hqf, hqT⟩, hsmall⟩ := hall α ⟨hpos, hα.2⟩
  set B : Set (Fin 2 → ℝ) := Set.univ.pi (fun i => Set.Icc (b i - ε0) (b i + ε0)) with hB
  have inbox : ∀ q' : Fin 2 → ℝ, (∀ i, 0 ≤ q' i) →
      R 0 (b 0) + R 1 (b 1) - δ0 ≤ R 0 (q' 0) + R 1 (q' 1) → q' ∈ B := by
    intro q' hq' hT
    have he := c2_each R b hopt q' hq' δ0 hT
    intro i _
    have := abs_lt.mp (hl i (q' i) (hq' i) (he i))
    constructor <;> linarith [this.1, this.2]
  set g : (Fin 2 → ℝ) → ℝ := fun p => |M 0 (p 0) - M 1 (p 1)| with hg
  set K : Set (Fin 2 → ℝ) := B ∩ g ⁻¹' Set.Iic ((1 - α) * |M 0 (b 0) - M 1 (b 1)|) with hK
  have hBc : IsCompact B := isCompact_univ_pi (fun i => isCompact_Icc)
  have hmaps : ∀ i, Set.MapsTo (fun p : Fin 2 → ℝ => p i) B (Set.Icc (b i - η) (b i + η)) := by
    intro i p hp
    have := hp i (Set.mem_univ _)
    constructor <;> linarith [this.1, this.2]
  have hMc : ∀ i, ContinuousOn (fun p : Fin 2 → ℝ => M i (p i)) B := fun i =>
    (hc i).2.comp (continuous_apply i).continuousOn (hmaps i)
  have hRc : ∀ i, ContinuousOn (fun p : Fin 2 → ℝ => R i (p i)) B := fun i =>
    (hc i).1.comp (continuous_apply i).continuousOn (hmaps i)
  have hgc : ContinuousOn g B := ((hMc 0).sub (hMc 1)).abs
  have hKc : IsCompact K :=
    hBc.of_isClosed_subset (hgc.preimage_isClosed_of_isClosed hBc.isClosed isClosed_Iic)
      Set.inter_subset_left
  have hqB : q ∈ B := inbox q hqf.1 (by nlinarith)
  have hqK : q ∈ K := ⟨hqB, hqf.2⟩
  have hTc : ContinuousOn (fun p : Fin 2 → ℝ => R 0 (p 0) + R 1 (p 1)) K :=
    ((hRc 0).add (hRc 1)).mono Set.inter_subset_left
  obtain ⟨p, hpK, hpmax⟩ := hKc.exists_isMaxOn ⟨q, hqK⟩ hTc
  have hpB := hpK.1
  refine ⟨p, ⟨fun i => ?_, hpK.2⟩, fun q' hq' => ?_⟩
  · have := hpB i (Set.mem_univ _)
    linarith [this.1, hε0b i]
  by_cases h : R 0 (b 0) + R 1 (b 1) - δ0 ≤ R 0 (q' 0) + R 1 (q' 1)
  · exact hpmax ⟨inbox q' hq'.1 h, hq'.2⟩
  · have := hpmax hqK
    have h' := lt_of_not_ge h
    change R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1) at this
    linarith

theorem c2_core (R M S : Fin 2 → ℝ → ℝ) (w b r mm σ v : Fin 2 → ℝ) (μ : ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcontM : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (S i) (σ i) (b i))
    (hv0 : r 0 * v 0 = μ * mm 0) (hv1 : r 1 * v 1 = -(μ * mm 1))
    (hvl : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1)))
    (hμΔ : 0 ≤ μ * (M 0 (b 0) - M 1 (b 1)))
    (P : ℝ → Fin 2 → ℝ)
    (hP : ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) :
    Tendsto (fun α =>
          ((R 0 (P α 0) + R 1 (P α 1) + w 0 * S 0 (P α 0) + w 1 * S 1 (P α 1)) -
            (R 0 (b 0) + R 1 (b 1) + w 0 * S 0 (b 0) + w 1 * S 1 (b 1))) / α)
        (𝓝[>] 0) (𝓝 (w 0 * σ 0 * v 0 + w 1 * σ 1 * v 1)) := by
  obtain ⟨εP, hεP, hPall⟩ := hP
  have hPev : ∀ᶠ α in 𝓝[>] (0:ℝ), (((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) ∧ 0 < α := by
    filter_upwards [Ioc_mem_nhdsGT hεP] with α hα using ⟨hPall α hα, hα.1⟩
  set Qs := r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 with hQs
  set T0 := R 0 (b 0) + R 1 (b 1) with hT0
  have hQs0 : Qs ≤ 0 := by
    have := hr 0; have := hr 1
    rw [hQs]; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  -- Step A: lower bound
  have hA : ∀ κ > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      T0 + (Qs - κ) * α ^ 2 ≤ R 0 (P α 0) + R 1 (P α 1) := by
    intro κ hκ
    filter_upwards [c2_lower R M b r mm v hb hcontM hr hRt hMd hmm hvl κ hκ, hPev]
      with α hq hP
    obtain ⟨q, hqf, hqT⟩ := hq
    exact le_trans hqT (hP.1.2 q hqf)
  -- Step B: localisation
  have hPt : ∀ i, Tendsto (fun α => P α i) (𝓝[>] 0) (𝓝 (b i)) := by
    intro i
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hl⟩ := hloc ε hε
    filter_upwards [hA 1 one_pos, c2_ev_small (-(Qs - 1)) δ hδ, hPev] with α h1 h2 h3
    have he := c2_each R b hopt (P α) h3.1.1.1 δ (by nlinarith)
    rw [Real.dist_eq]
    exact hl i (P α i) (h3.1.1.1 i) (he i)
  have hdt : ∀ i, Tendsto (fun α => P α i - b i) (𝓝[>] 0) (𝓝 0) := by
    intro i
    simpa using (hPt i).sub_const (b i)
  -- Step C: Taylor of R along P
  have hRo : ∀ i, (fun α => R i (P α i) - R i (b i) - r i / 2 * (P α i - b i) ^ 2) =o[𝓝[>] 0]
      (fun α => (P α i - b i) ^ 2) := by
    intro i
    refine ((hRt i).comp_tendsto (hdt i)).congr_left ?_
    intro α
    simp [Function.comp]
  have hRb : ∀ i, ∀ κ > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      |R i (P α i) - R i (b i) - r i / 2 * (P α i - b i) ^ 2| ≤ κ * (P α i - b i) ^ 2 := by
    intro i κ hκ
    filter_upwards [(hRo i).def hκ] with α h
    simpa [Real.norm_eq_abs] using h
  -- Step D: d = O(α)
  set C := 4 * (1 - Qs) / (-r 0) + 4 * (1 - Qs) / (-r 1) with hCdef
  have hr0 := hr 0
  have hr1 := hr 1
  have hC0 : 0 ≤ 4 * (1 - Qs) / (-r 0) := div_nonneg (by linarith) (by linarith)
  have hC1 : 0 ≤ 4 * (1 - Qs) / (-r 1) := div_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ C := by rw [hCdef]; linarith
  have hD : ∀ᶠ α in 𝓝[>] (0:ℝ), ∀ i, (P α i - b i) ^ 2 ≤ C * α ^ 2 := by
    filter_upwards [hA 1 one_pos, hRb 0 (-r 0 / 4) (by linarith), hRb 1 (-r 1 / 4) (by linarith)]
      with α h1 h2 h3
    have a2 := (abs_le.mp h2).2
    have a3 := (abs_le.mp h3).2
    have n0 : 0 ≤ (-r 0) * (P α 0 - b 0) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have n1 : 0 ≤ (-r 1) * (P α 1 - b 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have nα : 0 ≤ α ^ 2 := sq_nonneg α
    have k0 : (-r 0) * (P α 0 - b 0) ^ 2 ≤ 4 * (1 - Qs) * α ^ 2 := by linarith
    have k1 : (-r 1) * (P α 1 - b 1) ^ 2 ≤ 4 * (1 - Qs) * α ^ 2 := by linarith
    have l0 : (P α 0 - b 0) ^ 2 ≤ 4 * (1 - Qs) / (-r 0) * α ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
    have l1 : (P α 1 - b 1) ^ 2 ≤ 4 * (1 - Qs) / (-r 1) * α ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
    have m0 : 0 ≤ 4 * (1 - Qs) / (-r 0) * α ^ 2 := mul_nonneg hC0 nα
    have m1 : 0 ≤ 4 * (1 - Qs) / (-r 1) * α ^ 2 := mul_nonneg hC1 nα
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; rw [hCdef]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; rw [hCdef]; linarith
  have hO : ∀ i, (fun α => P α i - b i) =O[𝓝[>] 0] (fun α => α) := by
    intro i
    refine IsBigO.of_bound (Real.sqrt C) ?_
    filter_upwards [hD] with α h
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt hC, sq_abs]
    exact h i
  -- Step E: linearisations
  have hMo : ∀ i, (fun α => M i (P α i) - M i (b i) - mm i * (P α i - b i)) =o[𝓝[>] 0]
      (fun α => α) := fun i => c2_lin (M i) (mm i) (b i) (hMd i) (fun α => P α i) (hPt i) (hO i)
  have hSo : ∀ i, (fun α => S i (P α i) - S i (b i) - σ i * (P α i - b i)) =o[𝓝[>] 0]
      (fun α => α) := fun i => c2_lin (S i) (σ i) (b i) (hSd i) (fun α => P α i) (hPt i) (hO i)
  have hMb : ∀ i, ∀ κ > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      |M i (P α i) - M i (b i) - mm i * (P α i - b i)| ≤ κ * α := by
    intro i κ hκ
    filter_upwards [(hMo i).def hκ, hPev] with α h h'
    simpa [Real.norm_eq_abs, abs_of_pos h'.2] using h
  -- Step F: blow-up converges to v
  have hY : ∀ ε > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      -r 0 / 2 * (P α 0 - b 0 - α * v 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1 - α * v 1) ^ 2
        ≤ ε * α ^ 2 := by
    intro ε hε
    set L := 1 + 2 * C + 2 * |μ| with hLdef
    have hL : 0 < L := by rw [hLdef]; positivity
    set κ := ε / L with hκdef
    have hκ : 0 < κ := div_pos hε hL
    have hκL : κ * L = ε := div_mul_cancel₀ ε (ne_of_gt hL)
    filter_upwards [hA κ hκ, hRb 0 κ hκ, hRb 1 κ hκ, hD, hMb 0 κ hκ, hMb 1 κ hκ, hPev]
      with α hA' hR0 hR1 hD' hM0 hM1 hP'
    have hα := hP'.2
    have hfeas := hP'.1.1.2
    have r0a := abs_le.mp hR0
    have r1a := abs_le.mp hR1
    have q1 : -r 0 / 2 * (P α 0 - b 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1) ^ 2 ≤
        (κ - Qs) * α ^ 2 + κ * ((P α 0 - b 0) ^ 2 + (P α 1 - b 1) ^ 2) := by
      linarith [r0a.1, r0a.2, r1a.1, r1a.2]
    have q2 : κ * ((P α 0 - b 0) ^ 2 + (P α 1 - b 1) ^ 2) ≤ κ * (2 * C * α ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hκ.le
      linarith [hD' 0, hD' 1]
    have c1 : μ * (M 0 (P α 0) - M 1 (P α 1)) ≤ (1 - α) * (μ * (M 0 (b 0) - M 1 (b 1))) := by
      calc μ * (M 0 (P α 0) - M 1 (P α 1)) ≤ |μ * (M 0 (P α 0) - M 1 (P α 1))| := le_abs_self _
        _ = |μ| * |M 0 (P α 0) - M 1 (P α 1)| := abs_mul _ _
        _ ≤ |μ| * ((1 - α) * |M 0 (b 0) - M 1 (b 1)|) :=
            mul_le_mul_of_nonneg_left hfeas (abs_nonneg _)
        _ = (1 - α) * |μ * (M 0 (b 0) - M 1 (b 1))| := by rw [abs_mul]; ring
        _ = (1 - α) * (μ * (M 0 (b 0) - M 1 (b 1))) := by rw [abs_of_nonneg hμΔ]
    set e0 := M 0 (P α 0) - M 0 (b 0) - mm 0 * (P α 0 - b 0) with he0
    set e1 := M 1 (P α 1) - M 1 (b 1) - mm 1 * (P α 1 - b 1) with he1
    have c2 : -(μ * (e0 - e1)) ≤ |μ| * (2 * κ * α) := by
      calc -(μ * (e0 - e1)) ≤ |μ * (e0 - e1)| := neg_le_abs _
        _ = |μ| * |e0 - e1| := abs_mul _ _
        _ ≤ |μ| * (|e0| + |e1|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
        _ ≤ |μ| * (2 * κ * α) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have c3 : μ * (mm 0 * (P α 0 - b 0) - mm 1 * (P α 1 - b 1) + α * (M 0 (b 0) - M 1 (b 1)))
        ≤ |μ| * (2 * κ * α) := by
      have eq : μ * (mm 0 * (P α 0 - b 0) - mm 1 * (P α 1 - b 1) + α * (M 0 (b 0) - M 1 (b 1)))
          = μ * (M 0 (P α 0) - M 1 (P α 1)) - (1 - α) * (μ * (M 0 (b 0) - M 1 (b 1)))
            - μ * (e0 - e1) := by rw [he0, he1]; ring
      rw [eq]; linarith
    have c4 := mul_le_mul_of_nonneg_left c3 hα.le
    have iden : -r 0 / 2 * (P α 0 - b 0 - α * v 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1 - α * v 1) ^ 2
        = -r 0 / 2 * (P α 0 - b 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1) ^ 2 + α ^ 2 * Qs
          + α * (μ * (mm 0 * (P α 0 - b 0) - mm 1 * (P α 1 - b 1) + α * (M 0 (b 0) - M 1 (b 1))))
          := by
      rw [hQs]
      linear_combination (α * (P α 0 - b 0) - α ^ 2 * v 0) * hv0
        + (α * (P α 1 - b 1) - α ^ 2 * v 1) * hv1 - α ^ 2 * μ * hvl
    have fin : κ * L * α ^ 2 = ε * α ^ 2 := by rw [hκL]
    rw [iden]
    rw [hLdef] at fin
    linarith [q1, q2, c4, fin]
  have hconv : ∀ i, Tendsto (fun α => (P α i - b i) / α) (𝓝[>] 0) (𝓝 (v i)) := by
    intro i
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hri : 0 < -r i / 2 := by linarith [hr i]
    filter_upwards [hY ((-r i / 2) * (ε ^ 2 / 2)) (by positivity), hPev] with α h hP'
    have hα := hP'.2
    have hi : -r i / 2 * (P α i - b i - α * v i) ^ 2 ≤ (-r i / 2) * (ε ^ 2 / 2) * α ^ 2 := by
      have n0 : 0 ≤ -r 0 / 2 * (P α 0 - b 0 - α * v 0) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      have n1 : 0 ≤ -r 1 / 2 * (P α 1 - b 1 - α * v 1) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue] at h ⊢; linarith
      · simp only [Fin.mk_one, Fin.isValue] at h ⊢; linarith
    have hx : (P α i - b i - α * v i) ^ 2 < (ε * α) ^ 2 := by
      have : (P α i - b i - α * v i) ^ 2 ≤ (ε ^ 2 / 2) * α ^ 2 := by
        rw [mul_assoc] at hi
        exact le_of_mul_le_mul_left hi hri
      have hpos : 0 < ε ^ 2 * α ^ 2 := by positivity
      rw [mul_pow]
      linarith
    have hab := abs_lt_of_sq_lt_sq hx (by positivity)
    rw [Real.dist_eq]
    have : (P α i - b i) / α - v i = (P α i - b i - α * v i) / α := by
      field_simp
    rw [this, abs_div, abs_of_pos hα, div_lt_iff₀ hα]
    linarith
  -- Step G: assemble
  have hTo : (fun α => R 0 (P α 0) + R 1 (P α 1) - T0) =o[𝓝[>] 0] (fun α => α) := by
    refine IsBigO.trans_isLittleO ?_ c2_sq_o
    refine IsBigO.of_bound (1 - Qs) ?_
    filter_upwards [hA 1 one_pos, hPev] with α h1 h2
    have u0 := hopt 0 (P α 0) (h2.1.1.1 0)
    have u1 := hopt 1 (P α 1) (h2.1.1.1 1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg α), abs_le]
    constructor <;> nlinarith
  have hS : ∀ i, Tendsto (fun α => (S i (P α i) - S i (b i)) / α) (𝓝[>] 0) (𝓝 (σ i * v i)) := by
    intro i
    have h1 := ((hconv i).const_mul (σ i)).add (hSo i).tendsto_div_nhds_zero
    rw [add_zero] at h1
    refine h1.congr (fun α => ?_)
    ring
  have hall := (hTo.tendsto_div_nhds_zero.add ((hS 0).const_mul (w 0))).add
    ((hS 1).const_mul (w 1))
  have hlim : (0 : ℝ) + w 0 * (σ 0 * v 0) + w 1 * (σ 1 * v 1) = w 0 * σ 0 * v 0 + w 1 * σ 1 * v 1 := by
    ring
  rw [hlim] at hall
  refine hall.congr (fun α => ?_)
  simp only [hT0]
  ring

theorem core_sensitivity
    (R M S : Fin 2 → ℝ → ℝ) (w b r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (R i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (S i) (σ i) (b i))
    (hgap : M 0 (b 0) ≠ M 1 (b 1)) :
    (∃ ε > 0, ∀ α ∈ Set.Icc (0 : ℝ) ε, ∃ p : Fin 2 → ℝ,
      ((∀ i, 0 ≤ p i) ∧ |M 0 (p 0) - M 1 (p 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      ∀ q : Fin 2 → ℝ,
        ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
        R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1)) ∧
    ∀ P : ℝ → Fin 2 → ℝ,
      (∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) →
      Tendsto (fun α =>
          ((R 0 (P α 0) + R 1 (P α 1) + w 0 * S 0 (P α 0) + w 1 * S 1 (P α 1)) -
            (R 0 (b 0) + R 1 (b 1) + w 0 * S 0 (b 0) + w 1 * S 1 (b 1))) / α)
        (𝓝[>] 0)
        (𝓝 (w 0 * σ 0 * ((-(M 0 (b 0) - M 1 (b 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
            w 1 * σ 1 * (-((-(M 0 (b 0) - M 1 (b 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) := by
  have hcontM : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)) := by
    obtain ⟨η, hη, h⟩ := hcont
    exact ⟨η, hη, fun i => (h i).2⟩
  have hr0 := hr 0
  have hr1 := hr 1
  have hK : mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
    have a0 : mm 0 ^ 2 / r 0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr0.le
    have a1 : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr1.le
    rcases hmm with h | h
    · have : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (by positivity) hr0
      linarith
    · have : mm 1 ^ 2 / r 1 < 0 := div_neg_of_pos_of_neg (by positivity) hr1
      linarith
  set Δ := M 0 (b 0) - M 1 (b 1) with hΔ
  set K := mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 with hKdef
  set μ := -Δ / K with hμ
  have hK0 : K ≠ 0 := ne_of_lt hK
  have hr0' : r 0 ≠ 0 := ne_of_lt hr0
  have hr1' : r 1 ≠ 0 := ne_of_lt hr1
  have hμK : μ * K = -Δ := by rw [hμ, div_mul_cancel₀ _ hK0]
  have hμΔ : 0 ≤ μ * Δ := by
    have : μ * Δ = Δ ^ 2 / (-K) := by rw [hμ]; field_simp
    rw [this]; exact div_nonneg (sq_nonneg _) (by linarith)
  set v : Fin 2 → ℝ := ![μ * mm 0 / r 0, -(μ * mm 1 / r 1)] with hvdef
  have hv0 : r 0 * v 0 = μ * mm 0 := by
    show r 0 * (μ * mm 0 / r 0) = μ * mm 0
    field_simp
  have hv1 : r 1 * v 1 = -(μ * mm 1) := by
    show r 1 * -(μ * mm 1 / r 1) = -(μ * mm 1)
    field_simp
  have hvl : mm 0 * v 0 - mm 1 * v 1 = -Δ := by
    rw [← hμK]
    show mm 0 * (μ * mm 0 / r 0) - mm 1 * -(μ * mm 1 / r 1) = μ * K
    rw [hKdef]
    ring
  refine ⟨c2_exist R M b _ hb hopt hloc hcont
    (c2_lower R M b r mm v hb hcontM hr hRt hMd hmm hvl 1 one_pos), fun P hP => ?_⟩
  have := c2_core R M S w b r mm σ v μ hb hopt hloc hcontM hr hRt hMd hmm hSd hv0 hv1 hvl hμΔ P hP
  exact this

end CohenPriceFairness.LocalWelfare.Proofs

/-! # L1 — Lemma 1 for an arbitrary admissible market -/

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Set

namespace CohenPriceFairness.LocalWelfare.Proofs
open CohenPriceFairness.LocalWelfare

section L1measure
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma l1_D_le_one (p : ℝ) : (μ (Ici p)).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := μ) (s := Ici p))

lemma l1_D_anti {p q : ℝ} (h : p ≤ q) : (μ (Ici q)).toReal ≤ (μ (Ici p)).toReal :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ici_subset_Ici.mpr h))

lemma l1_D_usc (p η : ℝ) (hη : 0 < η) :
    ∀ᶠ q in 𝓝 p, (μ (Ici q)).toReal < (μ (Ici p)).toReal + η := by
  have ht := tendsto_measure_biInter_gt (μ := μ) (s := fun r : ℝ => Ici (p - r)) (a := 0)
    (fun r _ => measurableSet_Ici.nullMeasurableSet)
    (fun i j _ hij => Ici_subset_Ici.mpr (by linarith)) ⟨1, one_pos, measure_ne_top _ _⟩
  have hI : (⋂ r > (0:ℝ), Ici (p - r)) = Ici p := by
    ext x; simp only [mem_iInter, mem_Ici]
    constructor
    · intro h
      by_contra hx; push Not at hx
      have := h ((p - x) / 2) (by linarith); linarith
    · intro hx r hr; linarith
  rw [hI] at ht
  have ht' := (ENNReal.tendsto_toReal (measure_ne_top μ (Ici p))).comp ht
  have hev : ∀ᶠ r in 𝓝[>] (0:ℝ), (μ (Ici (p - r))).toReal < (μ (Ici p)).toReal + η :=
    ht'.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r, hr, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0' : 0 < r := hr0
  filter_upwards [Ioi_mem_nhds (show p - r < p by linarith)] with q hq
  exact lt_of_le_of_lt (l1_D_anti (le_of_lt hq)) hr

lemma l1_tail (hint : Integrable (fun v : ℝ => v) μ) :
    Tendsto (fun p : ℝ => p * (μ (Ici p)).toReal) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun p v => (Ici p).indicator (fun _ => p) v) (f := fun _ => (0:ℝ)) (fun v => |v|)
    (Eventually.of_forall fun p =>
      (aestronglyMeasurable_const.indicator measurableSet_Ici)) ?_ hint.abs ?_
  · simp only [integral_zero] at h
    refine h.congr' ?_
    filter_upwards with p
    rw [integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_comm]
    rfl
  · filter_upwards [eventually_ge_atTop 0] with p hp
    refine Eventually.of_forall fun v => ?_
    by_cases hv : p ≤ v
    · simp [indicator, hv, abs_of_nonneg hp, abs_of_nonneg (hp.trans hv)]
    · simp [indicator, hv]
  · refine Eventually.of_forall fun v => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop v] with p hp
    simp [indicator, not_le.mpr hp]

end L1measure

lemma l1_demand_nonneg (m : Market) (i : Fin 2) (p : ℝ) : 0 ≤ demand m i p :=
  ENNReal.toReal_nonneg

lemma l1_pos (m : Market) (hm : m.Admissible) (b : Prices)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i) (i : Fin 2) :
    0 < profit m i (b i) ∧ m.cost < b i ∧ 0 < demand m i (b i) := by
  have hc := hm.1
  have hd := (hm.2 i).1
  have hD := l1_demand_nonneg m i
  have hR : 0 < profit m i (b i) := by
    by_contra h; push Not at h
    have hmx := le_max_left m.cost (b i)
    have hmx2 := le_max_right m.cost (b i)
    have hp0 : 0 ≤ max m.cost (b i) + 1 := by linarith
    have hRp : 0 ≤ profit m i (max m.cost (b i) + 1) := by
      unfold profit
      have : 0 ≤ max m.cost (b i) + 1 - m.cost := by linarith
      have := hD (max m.cost (b i) + 1); positivity
    have := huniq i _ hp0 (h.trans hRp)
    linarith
  refine ⟨hR, ?_⟩
  have h1 : 0 < (b i - m.cost) * demand m i (b i) := by
    have : profit m i (b i) = m.population i * ((b i - m.cost) * demand m i (b i)) := by
      unfold profit; ring
    rw [this] at hR
    exact (mul_pos_iff_of_pos_left hd).mp hR
  rcases mul_pos_iff.mp h1 with h | h
  · exact ⟨by linarith [h.1], h.2⟩
  · exact absurd h.2 (not_lt.mpr (hD _))

lemma l1_R_bound (m : Market) (hm : m.Admissible) (i : Fin 2) (p q : ℝ) (hp : m.cost ≤ p) :
    profit m i q ≤ profit m i p + m.population i * |q - p| +
      m.population i * (p - m.cost) * (demand m i q - demand m i p) := by
  have := (hm.2 i).2.1
  have hd := (hm.2 i).1
  have hD0 := l1_demand_nonneg m i q
  have hD1 : demand m i q ≤ 1 := l1_D_le_one q
  have h1 : (q - p) * demand m i q ≤ |q - p| := by
    calc (q - p) * demand m i q ≤ |q - p| * demand m i q :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hD0
      _ ≤ |q - p| * 1 := mul_le_mul_of_nonneg_left hD1 (abs_nonneg _)
      _ = |q - p| := mul_one _
  have : profit m i q - profit m i p = m.population i * ((q - p) * demand m i q) +
      m.population i * (p - m.cost) * (demand m i q - demand m i p) := by
    unfold profit; ring
  have h2 := mul_le_mul_of_nonneg_left h1 hd.le
  linarith

lemma l1_R_usc (m : Market) (hm : m.Admissible) (i : Fin 2) (p : ℝ) (hp : m.cost ≤ p)
    (y : ℝ) (hy : profit m i p < y) : ∀ᶠ q in 𝓝 p, profit m i q < y := by
  have := (hm.2 i).2.1
  have hd := (hm.2 i).1
  set η := (y - profit m i p) / (2 * m.population i * (1 + (p - m.cost))) with hη
  have hpos : 0 < 2 * m.population i * (1 + (p - m.cost)) := by
    have : 0 < 1 + (p - m.cost) := by linarith
    positivity
  have hη0 : 0 < η := div_pos (by linarith) hpos
  have hηe : m.population i * η * (1 + (p - m.cost)) = (y - profit m i p) / 2 := by
    have : 1 + (p - m.cost) ≠ 0 := by linarith
    rw [hη]; field_simp
  filter_upwards [l1_D_usc (μ := m.law i) p η hη0, Metric.ball_mem_nhds p hη0] with q hq1 hq2
  have hq2' : |q - p| < η := hq2
  have hb := l1_R_bound m hm i p q hp
  have e1 : m.population i * |q - p| ≤ m.population i * η :=
    mul_le_mul_of_nonneg_left hq2'.le hd.le
  have e2 : m.population i * (p - m.cost) * (demand m i q - demand m i p) ≤
      m.population i * (p - m.cost) * η := by
    apply mul_le_mul_of_nonneg_left _ (by have := sub_nonneg.mpr hp; positivity)
    have : demand m i q < demand m i p + η := hq1
    linarith
  nlinarith

lemma l1_loc_i (m : Market) (hm : m.Admissible) (b : Prices) (hb : BaselineOptimal m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i) (i : Fin 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p → |p - b i| < ε := by
  have := (hm.2 i).2.1
  have hd := (hm.2 i).1
  have hc := hm.1
  obtain ⟨hR, hcb, hDb⟩ := l1_pos m hm b huniq i
  set Rb := profit m i (b i)
  -- tail
  have ht := (l1_tail (μ := m.law i) (hm.2 i).2.2.2).const_mul (m.population i)
  rw [mul_zero] at ht
  obtain ⟨M, hM⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hR)))
  have htail : ∀ p, 0 ≤ p → M ≤ p → profit m i p < Rb / 2 := by
    intro p hp hMp
    have := hM p hMp
    have hD0 := l1_demand_nonneg m i p
    have : profit m i p ≤ m.population i * (p * demand m i p) := by
      unfold profit
      have : (p - m.cost) * demand m i p ≤ p * demand m i p :=
        mul_le_mul_of_nonneg_right (by linarith) hD0
      have := mul_le_mul_of_nonneg_left this hd.le
      linarith
    simp only [demand] at *
    linarith
  set K := Icc m.cost M ∩ {p | ε ≤ |p - b i|} with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hgapK : ∃ δ' > 0, ∀ p ∈ K, profit m i p + δ' ≤ Rb := by
    rcases K.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · have husc : UpperSemicontinuousOn (profit m i) K := by
        intro p hp y hy
        exact (l1_R_usc m hm i p hp.1.1 y hy).filter_mono nhdsWithin_le_nhds
      obtain ⟨p0, hp0, hmax⟩ := husc.exists_isMaxOn h hKc
      have hle := (hb i).2 p0 (hc.trans hp0.1.1)
      have hne : profit m i p0 ≠ Rb := by
        intro heq
        have := huniq i p0 (hc.trans hp0.1.1) heq.ge
        have h2 : ε ≤ |p0 - b i| := hp0.2
        rw [this, sub_self, abs_zero] at h2
        linarith
      refine ⟨Rb - profit m i p0, by
        have := lt_of_le_of_ne hle hne; linarith, fun p hp => ?_⟩
      have := hmax hp
      simp only [mem_ofPred_eq] at this
      linarith
  obtain ⟨δ', hδ', hK'⟩ := hgapK
  refine ⟨min (Rb / 2) (δ' / 2), lt_min (half_pos hR) (half_pos hδ'), fun p hp hRp => ?_⟩
  have hm1 := min_le_left (Rb / 2) (δ' / 2)
  have hm2 := min_le_right (Rb / 2) (δ' / 2)
  have hpc : m.cost ≤ p := by
    by_contra h; push Not at h
    have : profit m i p ≤ 0 := by
      unfold profit
      have : m.population i * (p - m.cost) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hd.le (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg this (l1_demand_nonneg m i p)
    linarith
  have hpM : p ≤ M := by
    by_contra h; push Not at h
    have := htail p hp h.le
    linarith
  by_contra h; push Not at h
  have := hK' p ⟨⟨hpc, hpM⟩, h⟩
  linarith

lemma l1_loc (m : Market) (hm : m.Admissible) (b : Prices) (hb : BaselineOptimal m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i) :
    ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε := by
  intro ε hε
  obtain ⟨δ0, h0, H0⟩ := l1_loc_i m hm b hb huniq 0 ε hε
  obtain ⟨δ1, h1, H1⟩ := l1_loc_i m hm b hb huniq 1 ε hε
  refine ⟨min δ0 δ1, lt_min h0 h1, fun i p hp hRp => ?_⟩
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · exact H0 p hp (le_trans (by linarith [min_le_left δ0 δ1]) hRp)
  · exact H1 p hp (le_trans (by linarith [min_le_right δ0 δ1]) hRp)

/-- Second-order Peano expansion at a critical point. -/
lemma l1_taylor (f : ℝ → ℝ) (x : ℝ) (hf : TwiceDifferentiableAt f x) (h0 : deriv f x = 0) :
    (fun h => f (x + h) - f x - deriv (deriv f) x / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2) := by
  obtain ⟨hev, hd2⟩ := hf
  set a := deriv (deriv f) x
  have ho := hd2.hasDerivAt.isLittleO
  rw [Asymptotics.isLittleO_iff] at ho ⊢
  intro ε hε
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp ((ho hε).and hev)
  rw [Metric.eventually_nhds_iff]
  refine ⟨ρ, hρ, fun h hh => ?_⟩
  have hh' : |h| < ρ := by simpa using hh
  have hsub : ∀ t ∈ Icc (-|h|) |h|, dist (x + t) x < ρ := by
    intro t ht
    rw [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs]
    exact lt_of_le_of_lt (abs_le.mpr ht) hh'
  have key : ∀ t ∈ Icc (-|h|) |h|, HasDerivWithinAt (fun t => f (x + t) - f x - a / 2 * t ^ 2)
      (deriv f (x + t) - a * t) (Icc (-|h|) |h|) t := by
    intro t ht
    have hdf := ((hball (hsub t ht)).2).hasDerivAt
    have h1 := hdf.comp_const_add x t
    have h2 : HasDerivAt (fun t : ℝ => a / 2 * t ^ 2) (a / 2 * (2 * t)) t := by
      have := (hasDerivAt_pow 2 t).const_mul (a / 2)
      simpa using this
    have h3 := (h1.sub_const (f x)).sub h2
    exact h3.hasDerivWithinAt.congr_deriv (by ring)
  have bound : ∀ t ∈ Icc (-|h|) |h|, ‖deriv f (x + t) - a * t‖ ≤ ε * |h| := by
    intro t ht
    have := (hball (hsub t ht)).1
    rw [h0] at this
    simp only [add_sub_cancel_left, sub_zero, smul_eq_mul, Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs, mul_comm a t]
    exact this.trans (mul_le_mul_of_nonneg_left (abs_le.mpr ht) hε.le)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le key bound (convex_Icc _ _)
    (x := 0) (y := h) ⟨by simp, by simp⟩ ⟨neg_abs_le h, le_abs_self h⟩
  simp only [add_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, sub_zero, Real.norm_eq_abs] at hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  calc _ ≤ ε * |h| * |h| := hm
    _ = ε * |h| ^ 2 := by ring

/-- The surplus has `-demand` as a subgradient. -/
lemma l1_surplus_sub (m : Market) (hm : m.Admissible) (i : Fin 2) (b p : ℝ) :
    surplus m i b - (p - b) * demand m i b ≤ surplus m i p := by
  have := (hm.2 i).2.1
  have hint := (hm.2 i).2.2.2
  have i1 : Integrable (fun v => max (v - p) 0) (m.law i) := (hint.sub (integrable_const p)).pos_part
  have i2 : Integrable (fun v => max (v - b) 0) (m.law i) := (hint.sub (integrable_const b)).pos_part
  have i3 : Integrable ((Ici b).indicator (fun _ => -(p - b))) (m.law i) :=
    (integrable_const _).indicator measurableSet_Ici
  have hmono : ∫ v, (Ici b).indicator (fun _ => -(p - b)) v ∂m.law i ≤
      ∫ v, (max (v - p) 0 - max (v - b) 0) ∂m.law i := by
    apply integral_mono i3 (i1.sub i2)
    intro v
    simp only [Pi.sub_apply]
    by_cases hv : b ≤ v
    · simp only [indicator, mem_Ici, hv, if_true]
      rw [max_eq_left (show 0 ≤ v - b by linarith)]
      have := le_max_left (v - p) 0
      linarith
    · simp only [indicator, mem_Ici, hv, if_false]
      rw [max_eq_right (show v - b ≤ 0 by linarith)]
      have := le_max_right (v - p) 0
      linarith
  rw [integral_indicator_const _ measurableSet_Ici, integral_sub i1 i2, smul_eq_mul] at hmono
  unfold surplus demand
  have : (m.law i).real (Ici b) = (m.law i (Ici b)).toReal := rfl
  rw [this] at hmono
  linarith

lemma l1_surplus_deriv (m : Market) (hm : m.Admissible) (i : Fin 2) (x : ℝ)
    (hS : DifferentiableAt ℝ (surplus m i) x) :
    HasDerivAt (surplus m i) (-demand m i x) x := by
  have hd := hS.hasDerivAt
  have hg : HasDerivAt (fun p => surplus m i p + p * demand m i x)
      (deriv (surplus m i) x + 1 * demand m i x) x :=
    hd.add ((hasDerivAt_id x).mul_const _)
  have hmin : IsLocalMin (fun p => surplus m i p + p * demand m i x) x := by
    refine Eventually.of_forall fun p => ?_
    have := l1_surplus_sub m hm i x p
    show surplus m i x + x * demand m i x ≤ surplus m i p + p * demand m i x
    nlinarith
  have := hmin.hasDerivAt_eq_zero hg
  have : deriv (surplus m i) x = -demand m i x := by linarith
  rw [← this]; exact hd

lemma l1_sign (w d r mm : Fin 2 → ℝ) (G : ℝ) (hr : ∀ i, r i < 0) (hmm0 : mm 0 ≠ 0)
    (hG : G < 0) :
    (0 < w 0 * (-d 0) * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * (-d 1) * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1))) ↔
    w 1 * d 1 * mm 1 * r 0 - w 0 * d 0 * mm 0 * r 1 < 0 := by
  have hr0 := hr 0
  have hr1 := hr 1
  have hK : mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
    have a : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (by positivity) hr0
    have b : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr1.le
    linarith
  have hc : 0 < G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1) / (r 0 * r 1) :=
    div_pos (div_pos_of_neg_of_neg hG hK) (mul_pos_of_neg_of_neg hr0 hr1)
  have heq : w 0 * (-d 0) * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * (-d 1) * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) =
      G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1) / (r 0 * r 1) *
        -(w 1 * d 1 * mm 1 * r 0 - w 0 * d 0 * mm 0 * r 1) := by
    have := hr0.ne; have := hr1.ne; have := hK.ne
    field_simp
    ring
  rw [heq, mul_pos_iff_of_pos_left hc, neg_pos]


theorem l1_ub_claim (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop) (r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (metricValue m k i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - r i / 2 * h ^ 2)
      =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (surplus m i) (σ i) (b i))
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : C (m.population 0 * σ 0 * ((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      m.population 1 * σ 1 * (-((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) :
    SensitivityClaim m b k C := by
  obtain ⟨h1, h2⟩ := core_sensitivity (profit m) (metricValue m k) (surplus m) m.population
    b r mm σ hb hopt hloc hcont hr hRt hMd hmm hSd hgap
  refine ⟨?_, ?_⟩
  · obtain ⟨ε, hε, H⟩ := h1
    classical
    let P : ℝ → Prices := fun α =>
      if α = 0 then b else if h : α ∈ Set.Icc (0:ℝ) ε then Classical.choose (H α h) else b
    refine ⟨P, by simp [P], min ε 1, lt_min hε one_pos, min_le_right _ _, ?_⟩
    intro α hα
    have hα1 : α ∈ Set.Icc (0:ℝ) 1 := ⟨hα.1, hα.2.trans (min_le_right _ _)⟩
    by_cases h0 : α = 0
    · subst h0
      have hP : P 0 = b := by simp [P]
      rw [hP]
      refine ⟨⟨hα1, fun i => (hb i).le, ?_⟩, ?_⟩
      · simp
      · intro q hq
        exact add_le_add (hopt 0 _ (hq.2.1 0)) (hopt 1 _ (hq.2.1 1))
    · have hαε : α ∈ Set.Icc (0:ℝ) ε := ⟨hα.1, hα.2.trans (min_le_left _ _)⟩
      have hP : P α = Classical.choose (H α hαε) := by simp only [P, if_neg h0, dif_pos hαε]
      obtain ⟨hfeas, hmax⟩ := Classical.choose_spec (H α hαε)
      rw [hP]
      refine ⟨⟨hα1, hfeas.1, hfeas.2⟩, ?_⟩
      intro q hq
      exact hmax q ⟨hq.2.1, hq.2.2⟩
  · rintro P ⟨hP0, ε, hε, hε1, hP⟩
    refine ⟨_, ?_, hC⟩
    have hyp : ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |metricValue m k 0 (P α 0) - metricValue m k 1 (P α 1)| ≤
            (1 - α) * |metricValue m k 0 (b 0) - metricValue m k 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |metricValue m k 0 (q 0) - metricValue m k 1 (q 1)| ≤
            (1 - α) * |metricValue m k 0 (b 0) - metricValue m k 1 (b 1)|) →
          profit m 0 (q 0) + profit m 1 (q 1) ≤ profit m 0 (P α 0) + profit m 1 (P α 1) := by
      refine ⟨ε, hε, fun α hα => ?_⟩
      have hαI : α ∈ Set.Icc (0:ℝ) ε := Set.Ioc_subset_Icc_self hα
      obtain ⟨⟨_, hnn, hg⟩, hmax⟩ := hP α hαI
      exact ⟨⟨hnn, hg⟩, fun q hq => hmax q ⟨⟨hαI.1, hαI.2.trans hε1⟩, hq.1, hq.2⟩⟩
    have := h2 P hyp
    show Tendsto (fun α => (welfare m (P α) - welfare m (P 0)) / α) _ _
    rw [hP0]
    exact this


lemma l1_eta (x : ℝ) {P : ℝ → Prop} (h : ∀ᶠ y in 𝓝 x, P y) :
    ∃ η > 0, ∀ y ∈ Icc (x - η) (x + η), P y := by
  obtain ⟨ρ, hρ, H⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ρ / 2, half_pos hρ, fun y hy => H ?_⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]

theorem l1_claim (m : Market) (hm : m.Admissible) (b : Prices) (hb : BaselineOptimal m b)
    (hr : LemmaRegularity m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i)
    (hcurv : ∀ i, deriv (deriv (profit m i)) (b i) < 0)
    (k : Metric) (C : ℝ → Prop) (mm : Fin 2 → ℝ)
    (hMev : ∀ i, ∀ᶠ y in 𝓝 (b i), ContinuousAt (metricValue m k i) y)
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : C (m.population 0 * (-demand m 0 (b 0)) *
        ((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
          (mm 0 ^ 2 / deriv (deriv (profit m 0)) (b 0) +
            mm 1 ^ 2 / deriv (deriv (profit m 1)) (b 1))) * mm 0 /
          deriv (deriv (profit m 0)) (b 0)) +
      m.population 1 * (-demand m 1 (b 1)) *
        (-((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
          (mm 0 ^ 2 / deriv (deriv (profit m 0)) (b 0) +
            mm 1 ^ 2 / deriv (deriv (profit m 1)) (b 1))) * mm 1 /
          deriv (deriv (profit m 1)) (b 1))))) :
    SensitivityClaim m b k C := by
  have hpos := l1_pos m hm b huniq
  have hb0 : ∀ i, 0 < b i := fun i => lt_of_le_of_lt hm.1 (hpos i).2.1
  have hev : ∀ i, ∀ᶠ y in 𝓝 (b i),
      ContinuousAt (profit m i) y ∧ ContinuousAt (metricValue m k i) y :=
    fun i => ((hr i).2.2.2.1.1.mono fun y hy => hy.continuousAt).and (hMev i)
  obtain ⟨η0, hη0, H0⟩ := l1_eta (b 0) (hev 0)
  obtain ⟨η1, hη1, H1⟩ := l1_eta (b 1) (hev 1)
  have hcont : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (metricValue m k i) (Set.Icc (b i - η) (b i + η)) := by
    refine ⟨min η0 η1, lt_min hη0 hη1, fun i => ?_⟩
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hm0 := min_le_left η0 η1
    have hm1 := min_le_right η0 η1
    rcases hi with rfl | rfl
    · have hs : Icc (b 0 - min η0 η1) (b 0 + min η0 η1) ⊆ Icc (b 0 - η0) (b 0 + η0) :=
        Icc_subset_Icc (by linarith) (by linarith)
      exact ⟨fun y hy => (H0 y (hs hy)).1.continuousWithinAt,
        fun y hy => (H0 y (hs hy)).2.continuousWithinAt⟩
    · have hs : Icc (b 1 - min η0 η1) (b 1 + min η0 η1) ⊆ Icc (b 1 - η1) (b 1 + η1) :=
        Icc_subset_Icc (by linarith) (by linarith)
      exact ⟨fun y hy => (H1 y (hs hy)).1.continuousWithinAt,
        fun y hy => (H1 y (hs hy)).2.continuousWithinAt⟩
  have hcrit : ∀ i, deriv (profit m i) (b i) = 0 := by
    intro i
    have hmax : IsLocalMax (profit m i) (b i) := by
      filter_upwards [Ioi_mem_nhds (hb0 i)] with p hp
      exact (hb i).2 p (le_of_lt hp)
    exact hmax.deriv_eq_zero
  exact l1_ub_claim m b k C (fun i => deriv (deriv (profit m i)) (b i)) mm
    (fun i => -demand m i (b i))
    hb0 (fun i => (hb i).2) (l1_loc m hm b hb huniq) hcont hcurv
    (fun i => l1_taylor _ _ (hr i).2.2.2.1 (hcrit i)) hMd hmm
    (fun i => l1_surplus_deriv m hm i (b i) (hr i).2.1.1.self_of_nhds) hgap hC

theorem lemma_1_nondegenerate (m : Market) (hm : m.Admissible) (b : Prices)
    (hb : BaselineOptimal m b) (hr : LemmaRegularity m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i)
    (hcurv : ∀ i, deriv (deriv (profit m i)) (b i) < 0) :
    (b 0 < b 1 → SensitivityClaim m b .price (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (demand m 0 (b 0) < demand m 1 (b 1) → (∀ i, deriv (demand m i) (b i) ≠ 0) →
      SensitivityClaim m b .demand (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (demand m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (demand m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (surplus m 0 (b 0) < surplus m 1 (b 1) → SensitivityClaim m b .surplus (fun D =>
      (0 < D ↔
        m.population 1 * (demand m 1 (b 1)) ^ 2 * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * (demand m 0 (b 0)) ^ 2 * deriv (deriv (profit m 1)) (b 1) > 0))) ∧
    (nonbuyer m 0 (b 0) < nonbuyer m 1 (b 1) → (∀ i, deriv (nonbuyer m i) (b i) ≠ 0) →
      SensitivityClaim m b .nonbuyer (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (nonbuyer m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (nonbuyer m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0))) := by
  have hpos := l1_pos m hm b huniq
  have hS : ∀ i, HasDerivAt (surplus m i) (-demand m i (b i)) (b i) :=
    fun i => l1_surplus_deriv m hm i (b i) (hr i).2.1.1.self_of_nhds
  refine ⟨fun h01 => ?_, fun h01 hd => ?_, fun h01 => ?_, fun h01 hd => ?_⟩
  · refine l1_claim m hm b hb hr huniq hcurv .price _ (fun _ => 1)
      (fun i => Eventually.of_forall fun y => continuousAt_id) (fun i => hasDerivAt_id (b i))
      (Or.inl one_ne_zero) (ne_of_lt h01) ?_
    have h := l1_sign m.population (fun i => demand m i (b i))
      (fun i => deriv (deriv (profit m i)) (b i)) (fun _ => 1)
      (metricValue m .price 0 (b 0) - metricValue m .price 1 (b 1)) hcurv one_ne_zero
      (by show b 0 - b 1 < 0; linarith)
    exact h.trans (by simp only [mul_one])
  · refine l1_claim m hm b hb hr huniq hcurv .demand _ (fun i => deriv (demand m i) (b i))
      (fun i => (hr i).1.1.mono fun y hy => hy.continuousAt)
      (fun i => (hr i).1.1.self_of_nhds.hasDerivAt)
      (Or.inl (hd 0)) (ne_of_lt h01) ?_
    exact l1_sign m.population (fun i => demand m i (b i))
      (fun i => deriv (deriv (profit m i)) (b i)) (fun i => deriv (demand m i) (b i))
      (metricValue m .demand 0 (b 0) - metricValue m .demand 1 (b 1)) hcurv (hd 0)
      (by show demand m 0 (b 0) - demand m 1 (b 1) < 0; linarith)
  · refine l1_claim m hm b hb hr huniq hcurv .surplus _ (fun i => -demand m i (b i))
      (fun i => (hr i).2.1.1.mono fun y hy => hy.continuousAt) hS
      (Or.inl (neg_ne_zero.mpr (hpos 0).2.2.ne')) (ne_of_lt h01) ?_
    have h := l1_sign m.population (fun i => demand m i (b i))
      (fun i => deriv (deriv (profit m i)) (b i)) (fun i => -demand m i (b i))
      (metricValue m .surplus 0 (b 0) - metricValue m .surplus 1 (b 1)) hcurv
      (neg_ne_zero.mpr (hpos 0).2.2.ne')
      (by show surplus m 0 (b 0) - surplus m 1 (b 1) < 0; linarith)
    refine h.trans ?_
    simp only [gt_iff_lt]
    constructor <;> intro h' <;> nlinarith [h']
  · refine l1_claim m hm b hb hr huniq hcurv .nonbuyer _ (fun i => deriv (nonbuyer m i) (b i))
      (fun i => (hr i).2.2.1.1.mono fun y hy => hy.continuousAt)
      (fun i => (hr i).2.2.1.1.self_of_nhds.hasDerivAt)
      (Or.inl (hd 0)) (ne_of_lt h01) ?_
    exact l1_sign m.population (fun i => demand m i (b i))
      (fun i => deriv (deriv (profit m i)) (b i)) (fun i => deriv (nonbuyer m i) (b i))
      (metricValue m .nonbuyer 0 (b 0) - metricValue m .nonbuyer 1 (b 1)) hcurv (hd 0)
      (by show nonbuyer m 0 (b 0) - nonbuyer m 1 (b 1) < 0; linarith)

end CohenPriceFairness.LocalWelfare.Proofs


open CohenPriceFairness.LocalWelfare

theorem solution (m : Market) (hm : m.Admissible) (b : Prices)
    (hb : BaselineOptimal m b) (hr : LemmaRegularity m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i)
    (hcurv : ∀ i, deriv (deriv (profit m i)) (b i) < 0) :
    (b 0 < b 1 → SensitivityClaim m b .price (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (demand m 0 (b 0) < demand m 1 (b 1) → (∀ i, deriv (demand m i) (b i) ≠ 0) →
      SensitivityClaim m b .demand (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (demand m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (demand m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (surplus m 0 (b 0) < surplus m 1 (b 1) → SensitivityClaim m b .surplus (fun D =>
      (0 < D ↔
        m.population 1 * (demand m 1 (b 1)) ^ 2 * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * (demand m 0 (b 0)) ^ 2 * deriv (deriv (profit m 1)) (b 1) > 0))) ∧
    (nonbuyer m 0 (b 0) < nonbuyer m 1 (b 1) → (∀ i, deriv (nonbuyer m i) (b i) ≠ 0) →
      SensitivityClaim m b .nonbuyer (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (nonbuyer m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (nonbuyer m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0))) :=
  CohenPriceFairness.LocalWelfare.Proofs.lemma_1_nondegenerate m hm b hb hr huniq hcurv

#print axioms solution
