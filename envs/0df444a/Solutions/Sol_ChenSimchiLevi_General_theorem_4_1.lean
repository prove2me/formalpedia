-- Prove2me | solution 1 for ChenSimchiLevi.General.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T05:10:04.276854+00:00
-- url     : https://prove2.me/submissions/f56f6aed-6278-4ca2-8ab8-55a9a4dcb839

import Mathlib
import Definitions.Def_ChenSimchiLevi_General_Model
import Definitions.Def_ChenSimchiLevi_General_SymKConvex
import Definitions.Def_ChenSimchiLevi_General_OrderEnvelope

set_option autoImplicit false

namespace ChenSimchiLevi.General

open MeasureTheory Filter Set Topology

/-! ### Section A: polynomial-growth integrals -/

theorem csl_pow_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have h1 : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  have h2 : (a + b) ^ n ≤ (2 * max a b) ^ n := pow_le_pow_left₀ (by linarith) h1 n
  have h3 : (max a b) ^ n ≤ a ^ n + b ^ n := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; have := pow_nonneg ha n; linarith
    · rw [max_eq_left h]; have := pow_nonneg hb n; linarith
  calc (a + b) ^ n ≤ (2 * max a b) ^ n := h2
    _ = 2 ^ n * (max a b) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (a ^ n + b ^ n) := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- the shock `ε₁ d + ε₂` is bounded in absolute value by its values at the endpoints -/
theorem csl_shock_le (p q d a b : ℝ) (hpd : p ≤ d) (hdq : d ≤ q) :
    |a * d + b| ≤ max |a * p + b| |a * q + b| := by
  rcases le_total 0 a with ha | ha
  · exact abs_le_max_abs_abs (by nlinarith) (by nlinarith)
  · rw [max_comm]; exact abs_le_max_abs_abs (by nlinarith) (by nlinarith)

theorem csl_shock_pow_le (p q d a b : ℝ) (ρ : ℕ) (hpd : p ≤ d) (hdq : d ≤ q) :
    |a * d + b| ^ ρ ≤ |a * p + b| ^ ρ + |a * q + b| ^ ρ := by
  have h := csl_shock_le p q d a b hpd hdq
  have h2 : |a * d + b| ^ ρ ≤ (max |a * p + b| |a * q + b|) ^ ρ :=
    pow_le_pow_left₀ (abs_nonneg _) h ρ
  rcases le_total |a * p + b| |a * q + b| with h3 | h3
  · rw [max_eq_right h3] at h2; have := pow_nonneg (abs_nonneg (a * p + b)) ρ; linarith
  · rw [max_eq_left h3] at h2; have := pow_nonneg (abs_nonneg (a * q + b)) ρ; linarith

/-- uniform polynomial bound on the integrand over a box -/
theorem csl_integrand_bound (φ : ℝ → ℝ) (C : ℝ) (ρ : ℕ) (hφ : ∀ z, |φ z| ≤ C * (1 + |z| ^ ρ))
    (Y p q y d a b : ℝ) (hy : |y| ≤ Y) (hpd : p ≤ d) (hdq : d ≤ q) :
    |φ (y - a * d - b)| ≤ |C| * (1 + 2 ^ ρ * (Y ^ ρ + (|a * p + b| ^ ρ + |a * q + b| ^ ρ))) := by
  have h1 := hφ (y - a * d - b)
  have e : y - a * d - b = y - (a * d + b) := by ring
  have h2 : |y - a * d - b| ≤ |y| + |a * d + b| := by
    rw [e]; exact abs_sub _ _
  have h3 : |y - a * d - b| ^ ρ ≤ (|y| + |a * d + b|) ^ ρ :=
    pow_le_pow_left₀ (abs_nonneg _) h2 ρ
  have h4 := csl_pow_add_le |y| |a * d + b| (abs_nonneg _) (abs_nonneg _) ρ
  have h5 : |y| ^ ρ ≤ Y ^ ρ := pow_le_pow_left₀ (abs_nonneg _) hy ρ
  have h6 := csl_shock_pow_le p q d a b ρ hpd hdq
  have h7 : 0 ≤ (2:ℝ) ^ ρ := by positivity
  have h8 : |y - a * d - b| ^ ρ ≤ 2 ^ ρ * (Y ^ ρ + (|a * p + b| ^ ρ + |a * q + b| ^ ρ)) := by
    calc |y - a * d - b| ^ ρ ≤ (|y| + |a * d + b|) ^ ρ := h3
      _ ≤ 2 ^ ρ * (|y| ^ ρ + |a * d + b| ^ ρ) := h4
      _ ≤ 2 ^ ρ * (Y ^ ρ + (|a * p + b| ^ ρ + |a * q + b| ^ ρ)) :=
        mul_le_mul_of_nonneg_left (by linarith) h7
  have h9 : 0 ≤ |y - a * d - b| ^ ρ := by positivity
  calc |φ (y - a * d - b)| ≤ C * (1 + |y - a * d - b| ^ ρ) := h1
    _ ≤ |C| * (1 + |y - a * d - b| ^ ρ) := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)

theorem csl_cont_comp (φ : ℝ → ℝ) (hφc : Continuous φ) (y d : ℝ) :
    Continuous (fun ε : ℝ × ℝ => φ (y - ε.1 * d - ε.2)) :=
  hφc.comp (by fun_prop)

theorem csl_integrable_comp (M : Model) (hA : M.Assumptions) (t : ℕ)
    (ht : t ∈ Finset.Icc 1 M.T) (φ : ℝ → ℝ) (hφc : Continuous φ) (C : ℝ)
    (hφ : ∀ z, |φ z| ≤ C * (1 + |z| ^ M.ρ)) (y d : ℝ)
    (hd : d ∈ Set.Icc (M.dlo t) (M.dhi t)) :
    Integrable (fun ε : ℝ × ℝ => φ (y - ε.1 * d - ε.2)) (M.μ t) := by
  have := hA.law_probability t ht
  have hmom := hA.demand_moment t ht d hd
  have hint : Integrable (fun ε : ℝ × ℝ => |C| * (1 + 2 ^ M.ρ *
      (|y| ^ M.ρ + (|ε.1 * d + ε.2| ^ M.ρ + |ε.1 * d + ε.2| ^ M.ρ)))) (M.μ t) := by
    refine Integrable.const_mul ((integrable_const 1).add (Integrable.const_mul
      ((integrable_const _).add (hmom.add hmom)) _)) _
  refine Integrable.mono' hint (csl_cont_comp φ hφc y d).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ε => ?_)
  rw [Real.norm_eq_abs]
  exact csl_integrand_bound φ C M.ρ hφ |y| d d y d ε.1 ε.2 le_rfl le_rfl le_rfl

theorem csl_continuousOn_integral (M : Model) (hA : M.Assumptions) (t : ℕ)
    (ht : t ∈ Finset.Icc 1 M.T) (φ : ℝ → ℝ) (hφc : Continuous φ) (C : ℝ)
    (hφ : ∀ z, |φ z| ≤ C * (1 + |z| ^ M.ρ)) :
    ContinuousOn (fun q : ℝ × ℝ => ∫ ε : ℝ × ℝ, φ (q.1 - ε.1 * q.2 - ε.2) ∂(M.μ t))
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) := by
  have := hA.law_probability t ht
  rintro ⟨y0, d0⟩ hx0
  have hpq := hA.demand_interval t ht
  have hmp := hA.demand_moment t ht (M.dlo t) ⟨le_rfl, hpq⟩
  have hmq := hA.demand_moment t ht (M.dhi t) ⟨hpq, le_rfl⟩
  have hbd : Integrable (fun ε : ℝ × ℝ => |C| * (1 + 2 ^ M.ρ * ((|y0| + 1) ^ M.ρ +
      (|ε.1 * M.dlo t + ε.2| ^ M.ρ + |ε.1 * M.dhi t + ε.2| ^ M.ρ)))) (M.μ t) :=
    Integrable.const_mul ((integrable_const 1).add (Integrable.const_mul
      ((integrable_const _).add (hmp.add hmq)) _)) _
  have hBcont : ContinuousOn (fun q' : ℝ × ℝ => ∫ ε : ℝ × ℝ, φ (q'.1 - ε.1 * q'.2 - ε.2) ∂(M.μ t))
      (Set.Icc (y0 - 1) (y0 + 1) ×ˢ Set.Icc (M.dlo t) (M.dhi t)) := by
    refine continuousOn_of_dominated (bound := fun ε : ℝ × ℝ => |C| * (1 + 2 ^ M.ρ *
      ((|y0| + 1) ^ M.ρ + (|ε.1 * M.dlo t + ε.2| ^ M.ρ + |ε.1 * M.dhi t + ε.2| ^ M.ρ))))
      ?_ ?_ hbd ?_
    · intro x _
      exact (csl_cont_comp φ hφc x.1 x.2).aestronglyMeasurable
    · rintro ⟨y, d⟩ ⟨hy, hd⟩
      refine Filter.Eventually.of_forall fun ε => ?_
      rw [Real.norm_eq_abs]
      have hyb : |y| ≤ |y0| + 1 := by
        have : |y| ≤ |y0| + |y - y0| := by
          have := abs_add_le y0 (y - y0)
          simpa using this
        have h2 : |y - y0| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
        linarith
      exact csl_integrand_bound φ C M.ρ hφ (|y0| + 1) (M.dlo t) (M.dhi t) y d ε.1 ε.2 hyb hd.1 hd.2
    · refine Filter.Eventually.of_forall fun ε => ?_
      exact (show Continuous (fun q' : ℝ × ℝ => φ (q'.1 - ε.1 * q'.2 - ε.2)) from
        hφc.comp (by fun_prop)).continuousOn
  have hmem : Set.Icc (y0 - 1) (y0 + 1) ×ˢ Set.Icc (M.dlo t) (M.dhi t) ∈
      𝓝[Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)] (y0, d0) := by
    rw [mem_nhdsWithin]
    refine ⟨Set.Ioo (y0 - 1) (y0 + 1) ×ˢ Set.univ, isOpen_Ioo.prod isOpen_univ,
      ⟨⟨by linarith, by linarith⟩, trivial⟩, ?_⟩
    rintro ⟨y, d⟩ ⟨⟨hy, -⟩, -, hd⟩
    exact ⟨⟨hy.1.le, hy.2.le⟩, hd⟩
  have hx0' : (y0, d0) ∈ Set.Icc (y0 - 1) (y0 + 1) ×ˢ Set.Icc (M.dlo t) (M.dhi t) :=
    ⟨⟨by linarith, by linarith⟩, hx0.2⟩
  exact (hBcont (y0, d0) hx0').mono_of_mem_nhdsWithin hmem

/-- Jensen: `h (y - d) ≤ G t y d`. -/
theorem csl_jensen (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (y d : ℝ) (hd : d ∈ Set.Icc (M.dlo t) (M.dhi t)) :
    M.h t (y - d) ≤ M.G t y d := by
  have := hA.law_probability t ht
  have hconv := hA.holding_convex t ht
  have hcont : ContinuousOn (M.h t) Set.univ := hconv.continuousOn isOpen_univ
  have hα := hA.alpha_integrable t ht
  have hβ := hA.beta_integrable t ht
  have hfi : Integrable (fun ε : ℝ × ℝ => y - ε.1 * d - ε.2) (M.μ t) :=
    ((integrable_const y).sub (hα.mul_const d)).sub hβ
  have hgi := hA.holding_integrable t ht y d hd
  have key := ConvexOn.map_integral_le (μ := M.μ t) (f := fun ε : ℝ × ℝ => y - ε.1 * d - ε.2)
    hconv hcont isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hfi hgi
  have h1 : Integrable (fun ε : ℝ × ℝ => y - ε.1 * d) (M.μ t) :=
    (integrable_const y).sub (hα.mul_const d)
  have e1 : ∫ ε : ℝ × ℝ, (y - ε.1 * d - ε.2) ∂(M.μ t) =
      (∫ ε : ℝ × ℝ, (y - ε.1 * d) ∂(M.μ t)) - ∫ ε : ℝ × ℝ, ε.2 ∂(M.μ t) := integral_sub h1 hβ
  have e2 : ∫ ε : ℝ × ℝ, (y - ε.1 * d) ∂(M.μ t) =
      (∫ _ε : ℝ × ℝ, y ∂(M.μ t)) - ∫ ε : ℝ × ℝ, ε.1 * d ∂(M.μ t) :=
    integral_sub (integrable_const y) (hα.mul_const d)
  have hint : ∫ ε : ℝ × ℝ, (y - ε.1 * d - ε.2) ∂(M.μ t) = y - d := by
    rw [e1, e2, integral_mul_const, hA.alpha_mean t ht, hA.beta_mean t ht]
    simp
  rw [hint] at key
  exact key

theorem csl_h_poly (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) :
    ∃ K : ℝ, ∀ z, |M.h t z| ≤ K * (1 + |z| ^ M.ρ) := by
  obtain ⟨C, hC⟩ := hA.holding_growth t ht
  have hpq := hA.demand_interval t ht
  set p := M.dlo t with hp
  have hpm : p ∈ Set.Icc (M.dlo t) (M.dhi t) := ⟨le_rfl, hpq⟩
  set L : ℝ := 1 + 2 ^ M.ρ + 2 ^ M.ρ * |p| ^ M.ρ with hL
  set K : ℝ := |C| * L with hK
  have hL0 : 0 ≤ L := by positivity
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _) hL0
  have hup : ∀ z, M.h t z ≤ K * (1 + |z| ^ M.ρ) := by
    intro z
    have h1 := csl_jensen M hA t ht (z + p) p hpm
    rw [add_sub_cancel_right] at h1
    have h2 := hC (z + p) p hpm
    have h3 : |z + p| ^ M.ρ ≤ 2 ^ M.ρ * (|z| ^ M.ρ + |p| ^ M.ρ) :=
      le_trans (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le z p) M.ρ)
        (csl_pow_add_le _ _ (abs_nonneg _) (abs_nonneg _) M.ρ)
    have ha : 0 ≤ |z| ^ M.ρ := by positivity
    have hb : (0:ℝ) ≤ 2 ^ M.ρ := by positivity
    have hc : 0 ≤ |p| ^ M.ρ := by positivity
    have h4 : C * (1 + |z + p| ^ M.ρ) ≤ |C| * (1 + 2 ^ M.ρ * (|z| ^ M.ρ + |p| ^ M.ρ)) :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
        (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C))
    have h5 : 1 + 2 ^ M.ρ * (|z| ^ M.ρ + |p| ^ M.ρ) ≤ L * (1 + |z| ^ M.ρ) := by
      rw [hL]; nlinarith [mul_nonneg hb ha, mul_nonneg (mul_nonneg hb hc) ha]
    have h6 := mul_le_mul_of_nonneg_left h5 (abs_nonneg C)
    calc M.h t z ≤ M.G t (z + p) p := h1
      _ ≤ C * (1 + |z + p| ^ M.ρ) := h2
      _ ≤ _ := h4
      _ ≤ |C| * (L * (1 + |z| ^ M.ρ)) := h6
      _ = K * (1 + |z| ^ M.ρ) := by rw [hK]; ring
  refine ⟨K + 2 * |M.h t 0|, fun z => ?_⟩
  have hzp : 0 ≤ |z| ^ M.ρ := by positivity
  have hconv := hA.holding_convex t ht
  have hmid : M.h t 0 ≤ (M.h t z + M.h t (-z)) / 2 := by
    have := hconv.2 (Set.mem_univ z) (Set.mem_univ (-z)) (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at this
    have e : (1/2 : ℝ) * z + 1/2 * (-z) = 0 := by ring
    rw [e] at this
    linarith
  have hup1 := hup z
  have hup2 := hup (-z)
  rw [abs_neg] at hup2
  have h0 := abs_nonneg (M.h t 0)
  have hle : M.h t 0 ≤ |M.h t 0| := le_abs_self _
  have hge : -|M.h t 0| ≤ M.h t 0 := neg_abs_le _
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg h0 hzp]
  · nlinarith [mul_nonneg h0 hzp]

/-! ### Section D: uniform coercivity and growth -/

theorem csl_unif_coercive (F : ℝ → ℝ → ℝ) (p q : ℝ)
    (hconv : ∀ d ∈ Set.Icc p q, ConvexOn ℝ Set.univ (fun y => F y d))
    (hcont : ∀ y, ContinuousOn (F y) (Set.Icc p q))
    (hco : ∀ d ∈ Set.Icc p q, Tendsto (fun y => F y d) atTop atTop) :
    ∀ L : ℝ, ∃ Y : ℝ, ∀ y ≥ Y, ∀ d ∈ Set.Icc p q, L ≤ F y d := by
  intro L
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ Y, ∃ y ≥ Y, ∃ d ∈ Icc p q, F y d < L
  choose yseq hyseq dseq hdseq hFseq using fun n : ℕ => hcon (n : ℝ)
  obtain ⟨dstar, hdstar, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hdseq
  have hy_top : Tendsto (fun n => yseq (φ n)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
    exact hyseq (φ n)
  -- key: F R d* ≤ F 0 d* for every R > 0
  have key : ∀ R : ℝ, 0 < R → F R dstar ≤ F 0 dstar := by
    intro R hR
    have hθ : Tendsto (fun n => R / yseq (φ n)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hy_top
    have hd0 : Tendsto (fun n => F 0 (dseq (φ n))) atTop (𝓝 (F 0 dstar)) :=
      ((hcont 0).continuousWithinAt hdstar).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hlim, Filter.Eventually.of_forall fun n => hdseq _⟩)
    have hdR : Tendsto (fun n => F R (dseq (φ n))) atTop (𝓝 (F R dstar)) :=
      ((hcont R).continuousWithinAt hdstar).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hlim, Filter.Eventually.of_forall fun n => hdseq _⟩)
    have hrhs : Tendsto (fun n => (1 - R / yseq (φ n)) * F 0 (dseq (φ n)) +
        (R / yseq (φ n)) * L) atTop (𝓝 (F 0 dstar)) := by
      have := (((tendsto_const_nhds (x := (1:ℝ))).sub hθ).mul hd0).add (hθ.mul_const L)
      simpa using this
    refine le_of_tendsto_of_tendsto hdR hrhs ?_
    filter_upwards [hy_top.eventually (eventually_gt_atTop R)] with n hn
    have hyp : 0 < yseq (φ n) := lt_trans hR hn
    set θ := R / yseq (φ n) with hθdef
    have hθ0 : 0 < θ := div_pos hR hyp
    have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hyp]; exact hn.le
    have hRe : (1 - θ) * 0 + θ * yseq (φ n) = R := by rw [hθdef]; field_simp; ring
    have h := (hconv (dseq (φ n)) (hdseq _)).2 (Set.mem_univ 0) (Set.mem_univ (yseq (φ n)))
      (show 0 ≤ 1 - θ by linarith) hθ0.le (by ring)
    simp only [smul_eq_mul] at h
    rw [hRe] at h
    have := hFseq (φ n)
    nlinarith
  -- contradiction with coercivity at d*
  obtain ⟨R, hR1, hR2⟩ := ((hco dstar hdstar).eventually (eventually_gt_atTop (F 0 dstar))).and
    (eventually_gt_atTop (0:ℝ)) |>.exists
  exact absurd (key R hR2) (not_le.2 hR1)

/-! ### Section C: symmetric concavity of the optimised profit -/

theorem csl_g_concave (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (V : ℝ → ℝ) (hVsym : SymKConvex M.k (fun x => -V x))
    (hint : ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      Integrable (fun ε : ℝ × ℝ => V (y - ε.1 * d - ε.2)) (M.μ t))
    (y0 y1 d0 d1 l : ℝ) (hd0 : d0 ∈ Set.Icc (M.dlo t) (M.dhi t))
    (hd1 : d1 ∈ Set.Icc (M.dlo t) (M.dhi t)) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    (1 - l) * M.gWith V t y0 d0 + l * M.gWith V t y1 d1 - max l (1 - l) * M.k ≤
      M.gWith V t ((1 - l) * y0 + l * y1) ((1 - l) * d0 + l * d1) := by
  have := hA.law_probability t ht
  have hl' : 0 ≤ 1 - l := by linarith
  have hdl : (1 - l) * d0 + l * d1 ∈ Set.Icc (M.dlo t) (M.dhi t) :=
    (convex_Icc _ _) hd0 hd1 hl' hl0 (by ring)
  -- revenue term
  have hrev : (1 - l) * (d0 * M.P t d0) + l * (d1 * M.P t d1) ≤
      ((1 - l) * d0 + l * d1) * M.P t ((1 - l) * d0 + l * d1) := by
    have := (hA.revenue_concave t ht).2 hd0 hd1 hl' hl0 (by ring)
    simpa [smul_eq_mul] using this
  -- integrands
  set F : ℝ → ℝ → ℝ × ℝ → ℝ := fun y d ε =>
    -M.h t (y - ε.1 * d - ε.2) + V (y - ε.1 * d - ε.2) with hF
  have hFint : ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t), Integrable (F y d) (M.μ t) :=
    fun y d hd => (hA.holding_integrable t ht y d hd).neg.add (hint y d hd)
  have hpt : ∀ ε : ℝ × ℝ, (1 - l) * F y0 d0 ε + l * F y1 d1 ε - max l (1 - l) * M.k ≤
      F ((1 - l) * y0 + l * y1) ((1 - l) * d0 + l * d1) ε := by
    intro ε
    have hz : (1 - l) * y0 + l * y1 - ε.1 * ((1 - l) * d0 + l * d1) - ε.2 =
        (1 - l) * (y0 - ε.1 * d0 - ε.2) + l * (y1 - ε.1 * d1 - ε.2) := by ring
    have hh := (hA.holding_convex t ht).2 (Set.mem_univ (y0 - ε.1 * d0 - ε.2))
      (Set.mem_univ (y1 - ε.1 * d1 - ε.2)) hl' hl0 (by ring)
    simp only [smul_eq_mul] at hh
    have hv := hVsym (y0 - ε.1 * d0 - ε.2) (y1 - ε.1 * d1 - ε.2) l ⟨hl0, hl1⟩
    simp only [hF]
    rw [hz]
    linarith
  have hmono : ∫ ε, ((1 - l) * F y0 d0 ε + l * F y1 d1 ε - max l (1 - l) * M.k) ∂(M.μ t) ≤
      ∫ ε, F ((1 - l) * y0 + l * y1) ((1 - l) * d0 + l * d1) ε ∂(M.μ t) := by
    refine integral_mono ?_ (hFint _ _ hdl) hpt
    exact (((hFint y0 d0 hd0).const_mul (1 - l)).add ((hFint y1 d1 hd1).const_mul l)).sub
      (integrable_const _)
  have hlin : ∫ ε, ((1 - l) * F y0 d0 ε + l * F y1 d1 ε - max l (1 - l) * M.k) ∂(M.μ t) =
      (1 - l) * ∫ ε, F y0 d0 ε ∂(M.μ t) + l * ∫ ε, F y1 d1 ε ∂(M.μ t) - max l (1 - l) * M.k := by
    have i0 : Integrable (fun ε => (1 - l) * F y0 d0 ε) (M.μ t) := (hFint y0 d0 hd0).const_mul (1 - l)
    have i1 : Integrable (fun ε => l * F y1 d1 ε) (M.μ t) := (hFint y1 d1 hd1).const_mul l
    have e1 : ∫ ε, ((1 - l) * F y0 d0 ε + l * F y1 d1 ε - max l (1 - l) * M.k) ∂(M.μ t) =
        (∫ ε, ((1 - l) * F y0 d0 ε + l * F y1 d1 ε) ∂(M.μ t)) -
          ∫ _ε : ℝ × ℝ, max l (1 - l) * M.k ∂(M.μ t) := integral_sub (i0.add i1) (integrable_const _)
    have e2 : ∫ ε, ((1 - l) * F y0 d0 ε + l * F y1 d1 ε) ∂(M.μ t) =
        (∫ ε, (1 - l) * F y0 d0 ε ∂(M.μ t)) + ∫ ε, l * F y1 d1 ε ∂(M.μ t) := integral_add i0 i1
    rw [e1, e2, integral_const_mul, integral_const_mul]
    simp
  unfold Model.gWith
  have e : M.c t * ((1 - l) * y0 + l * y1) = (1 - l) * (M.c t * y0) + l * (M.c t * y1) := by ring
  show (1 - l) * (d0 * M.P t d0 - M.c t * y0 + ∫ ε, F y0 d0 ε ∂(M.μ t)) +
      l * (d1 * M.P t d1 - M.c t * y1 + ∫ ε, F y1 d1 ε ∂(M.μ t)) - max l (1 - l) * M.k ≤
    ((1 - l) * d0 + l * d1) * M.P t ((1 - l) * d0 + l * d1) -
      M.c t * ((1 - l) * y0 + l * y1) + ∫ ε, F ((1 - l) * y0 + l * y1) ((1 - l) * d0 + l * d1) ε ∂(M.μ t)
  rw [e]
  linarith

theorem csl_gstar_attain (M : Model) (t : ℕ) (V : ℝ → ℝ) (hpq : M.dlo t ≤ M.dhi t)
    (hgcont : ContinuousOn (fun q : ℝ × ℝ => M.gWith V t q.1 q.2)
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t))) (y : ℝ) :
    ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      (∀ e ∈ Set.Icc (M.dlo t) (M.dhi t), M.gWith V t y e ≤ M.gWith V t y d) ∧
      M.GstarWith V t y = M.gWith V t y d := by
  have hc : ContinuousOn (M.gWith V t y) (Set.Icc (M.dlo t) (M.dhi t)) :=
    hgcont.comp (continuousOn_const.prodMk continuousOn_id) (fun d hd => ⟨Set.mem_univ _, hd⟩)
  obtain ⟨d, hd, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hpq) hc
  have hmax' : ∀ e ∈ Set.Icc (M.dlo t) (M.dhi t), M.gWith V t y e ≤ M.gWith V t y d :=
    fun e he => hmax he
  refine ⟨d, hd, hmax', ?_⟩
  unfold Model.GstarWith
  apply le_antisymm
  · exact csSup_le ⟨_, Set.mem_image_of_mem _ hd⟩ (Set.forall_mem_image.2 hmax')
  · exact le_csSup ⟨M.gWith V t y d, by rintro _ ⟨e, he, rfl⟩; exact hmax' e he⟩
      (Set.mem_image_of_mem _ hd)

theorem csl_sym_gstar_step (M : Model) (hA : M.Assumptions)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (V : ℝ → ℝ)
    (hVcont : Continuous V) (hVsym : SymKConvex M.k (fun x => -V x))
    (hVgrowth : ∃ C : ℝ, ∀ x, |V x| ≤ C * (1 + |x| ^ M.ρ))
    (hgcont : ContinuousOn (fun q : ℝ × ℝ => M.gWith V t q.1 q.2)
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t))) :
    SymKConvex M.k (fun y => -M.GstarWith V t y) := by
  obtain ⟨C, hC⟩ := hVgrowth
  have hpq := hA.demand_interval t ht
  have hint : ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      Integrable (fun ε : ℝ × ℝ => V (y - ε.1 * d - ε.2)) (M.μ t) :=
    fun y d hd => csl_integrable_comp M hA t ht V hVcont C hC y d hd
  intro y0 y1 l hl
  obtain ⟨hl0, hl1⟩ := hl
  obtain ⟨d0, hd0, -, he0⟩ := csl_gstar_attain M t V hpq hgcont y0
  obtain ⟨d1, hd1, -, he1⟩ := csl_gstar_attain M t V hpq hgcont y1
  obtain ⟨dl, hdl, hmaxl, hel⟩ := csl_gstar_attain M t V hpq hgcont ((1 - l) * y0 + l * y1)
  have hdm : (1 - l) * d0 + l * d1 ∈ Set.Icc (M.dlo t) (M.dhi t) :=
    (convex_Icc _ _) hd0 hd1 (by linarith) hl0 (by ring)
  have hk := csl_g_concave M hA t ht V hVsym hint y0 y1 d0 d1 l hd0 hd1 hl0 hl1
  have hle := hmaxl _ hdm
  show -M.GstarWith V t ((1 - l) * y0 + l * y1) ≤
    (1 - l) * -M.GstarWith V t y0 + l * -M.GstarWith V t y1 + max l (1 - l) * M.k
  rw [hel, he0, he1]
  linarith

/-! ### Section E: period analysis -/

theorem csl_rho_pos (M : Model) (hA : M.Assumptions) : 1 ≤ M.ρ := by
  have hT := hA.horizon
  have ht : 1 ∈ Finset.Icc 1 M.T := Finset.mem_Icc.2 ⟨le_rfl, hT⟩
  by_contra hcon
  have h0 : M.ρ = 0 := by omega
  obtain ⟨C, hC⟩ := hA.holding_growth 1 ht
  have hd : M.dlo 1 ∈ Set.Icc (M.dlo 1) (M.dhi 1) := ⟨le_rfl, hA.demand_interval 1 ht⟩
  obtain ⟨y, hy⟩ := ((hA.holding_coercive 1 ht (M.dlo 1) hd).eventually
    (eventually_gt_atTop (C * (1 + 1)))).exists
  have := hC y (M.dlo 1) hd
  rw [h0] at this
  simp only [pow_zero] at this
  linarith

theorem csl_c_nonneg (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) :
    0 ≤ M.c (t + 1) := by
  rw [Finset.mem_Icc] at ht
  by_cases h : t + 1 ≤ M.T
  · exact hA.unit_nonneg (t + 1) (Finset.mem_Icc.2 ⟨by omega, h⟩)
  · have : t + 1 = M.T + 1 := by omega
    rw [this, hA.terminal_unit]

theorem csl_G_convex_y (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (d : ℝ) (hd : d ∈ Set.Icc (M.dlo t) (M.dhi t)) :
    ConvexOn ℝ Set.univ (fun y => M.G t y d) := by
  refine ⟨convex_univ, fun y0 _ y1 _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hi0 := hA.holding_integrable t ht y0 d hd
  have hi1 := hA.holding_integrable t ht y1 d hd
  unfold Model.G
  have hle : ∫ ε : ℝ × ℝ, M.h t ((a * y0 + b * y1) - ε.1 * d - ε.2) ∂(M.μ t) ≤
      ∫ ε : ℝ × ℝ, (a * M.h t (y0 - ε.1 * d - ε.2) + b * M.h t (y1 - ε.1 * d - ε.2)) ∂(M.μ t) := by
    refine integral_mono (hA.holding_integrable t ht _ d hd) ((hi0.const_mul a).add (hi1.const_mul b))
      (fun ε => ?_)
    have hz : (a * y0 + b * y1) - ε.1 * d - ε.2 =
        a * (y0 - ε.1 * d - ε.2) + b * (y1 - ε.1 * d - ε.2) := by
      have : b = 1 - a := by linarith
      subst this; ring
    have := (hA.holding_convex t ht).2 (Set.mem_univ (y0 - ε.1 * d - ε.2))
      (Set.mem_univ (y1 - ε.1 * d - ε.2)) ha hb hab
    simp only [smul_eq_mul] at this
    rw [hz]; exact this
  have heq : ∫ ε : ℝ × ℝ, (a * M.h t (y0 - ε.1 * d - ε.2) + b * M.h t (y1 - ε.1 * d - ε.2)) ∂(M.μ t) =
      a * ∫ ε : ℝ × ℝ, M.h t (y0 - ε.1 * d - ε.2) ∂(M.μ t) +
        b * ∫ ε : ℝ × ℝ, M.h t (y1 - ε.1 * d - ε.2) ∂(M.μ t) := by
    rw [integral_add (hi0.const_mul a) (hi1.const_mul b), integral_const_mul, integral_const_mul]
  rw [heq] at hle
  exact hle

theorem csl_h_bound (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) :
    ∃ K : ℝ, ∀ z, |M.h t z| ≤ K * (1 + |z| ^ M.ρ) := csl_h_poly M hA t ht

theorem csl_h_cont (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) :
    Continuous (M.h t) := by
  have := (hA.holding_convex t ht).continuousOn isOpen_univ
  exact continuousOn_univ.1 this

theorem csl_G_contOn (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) :
    ContinuousOn (fun q : ℝ × ℝ => M.G t q.1 q.2) (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) := by
  obtain ⟨K, hK⟩ := csl_h_poly M hA t ht
  exact csl_continuousOn_integral M hA t ht (M.h t) (csl_h_cont M hA t ht) K hK

theorem csl_integral_poly_bound (M : Model) (hA : M.Assumptions) (t : ℕ)
    (ht : t ∈ Finset.Icc 1 M.T) (φ : ℝ → ℝ) (hφc : Continuous φ) (C : ℝ)
    (hφ : ∀ z, |φ z| ≤ C * (1 + |z| ^ M.ρ)) :
    ∃ C' : ℝ, ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      |∫ ε : ℝ × ℝ, φ (y - ε.1 * d - ε.2) ∂(M.μ t)| ≤ C' * (1 + |y| ^ M.ρ) := by
  have := hA.law_probability t ht
  have hpq := hA.demand_interval t ht
  have hmp := hA.demand_moment t ht (M.dlo t) ⟨le_rfl, hpq⟩
  have hmq := hA.demand_moment t ht (M.dhi t) ⟨hpq, le_rfl⟩
  set w : ℝ × ℝ → ℝ := fun ε => |ε.1 * M.dlo t + ε.2| ^ M.ρ + |ε.1 * M.dhi t + ε.2| ^ M.ρ with hw
  have hwi : Integrable w (M.μ t) := hmp.add hmq
  set m : ℝ := ∫ ε, w ε ∂(M.μ t) with hm
  have hm0 : 0 ≤ m := integral_nonneg (fun ε => by positivity)
  refine ⟨|C| * (1 + 2 ^ M.ρ + 2 ^ M.ρ * m), fun y d hd => ?_⟩
  set a0 : ℝ := |C| * (1 + 2 ^ M.ρ * |y| ^ M.ρ) with ha0
  set a1 : ℝ := |C| * 2 ^ M.ρ with ha1
  have hgi : Integrable (fun ε => a0 + a1 * w ε) (M.μ t) :=
    (integrable_const a0).add (hwi.const_mul a1)
  have hnorm := norm_integral_le_of_norm_le hgi
    (f := fun ε : ℝ × ℝ => φ (y - ε.1 * d - ε.2))
    (Filter.Eventually.of_forall fun ε => by
      rw [Real.norm_eq_abs]
      have := csl_integrand_bound φ C M.ρ hφ |y| (M.dlo t) (M.dhi t) y d ε.1 ε.2 le_rfl hd.1 hd.2
      calc |φ (y - ε.1 * d - ε.2)| ≤ _ := this
        _ = a0 + a1 * w ε := by rw [ha0, ha1, hw]; ring)
  have hint : ∫ ε, (a0 + a1 * w ε) ∂(M.μ t) = a0 + a1 * m := by
    rw [integral_add (integrable_const a0) (hwi.const_mul a1), integral_const, integral_const_mul]
    simp
    exact Or.inl rfl
  rw [hint, Real.norm_eq_abs] at hnorm
  refine le_trans hnorm ?_
  have hs : 0 ≤ |y| ^ M.ρ := by positivity
  have hb : (0:ℝ) ≤ 2 ^ M.ρ := by positivity
  rw [ha0, ha1]
  have : 0 ≤ |C| := abs_nonneg _
  nlinarith [mul_nonneg hb hs, mul_nonneg (mul_nonneg hb hm0) hs, mul_nonneg this (mul_nonneg hb hs),
    mul_nonneg this hm0, mul_nonneg this (mul_nonneg hb hm0), mul_nonneg this (mul_nonneg (mul_nonneg hb hm0) hs)]

/-! ### Section F: the period-t profit -/

theorem csl_mean (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (y d : ℝ) :
    Integrable (fun ε : ℝ × ℝ => y - ε.1 * d - ε.2) (M.μ t) ∧
    ∫ ε : ℝ × ℝ, (y - ε.1 * d - ε.2) ∂(M.μ t) = y - d := by
  have := hA.law_probability t ht
  have hα := hA.alpha_integrable t ht
  have hβ := hA.beta_integrable t ht
  have h1 : Integrable (fun ε : ℝ × ℝ => y - ε.1 * d) (M.μ t) :=
    (integrable_const y).sub (hα.mul_const d)
  refine ⟨h1.sub hβ, ?_⟩
  have e1 : ∫ ε : ℝ × ℝ, (y - ε.1 * d - ε.2) ∂(M.μ t) =
      (∫ ε : ℝ × ℝ, (y - ε.1 * d) ∂(M.μ t)) - ∫ ε : ℝ × ℝ, ε.2 ∂(M.μ t) := integral_sub h1 hβ
  have e2 : ∫ ε : ℝ × ℝ, (y - ε.1 * d) ∂(M.μ t) =
      (∫ _ε : ℝ × ℝ, y ∂(M.μ t)) - ∫ ε : ℝ × ℝ, ε.1 * d ∂(M.μ t) :=
    integral_sub (integrable_const y) (hα.mul_const d)
  rw [e1, e2, integral_mul_const, hA.alpha_mean t ht, hA.beta_mean t ht]
  simp

theorem csl_g_split (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (V : ℝ → ℝ) (hint : ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      Integrable (fun ε : ℝ × ℝ => V (y - ε.1 * d - ε.2)) (M.μ t))
    (y d : ℝ) (hd : d ∈ Set.Icc (M.dlo t) (M.dhi t)) :
    M.gWith V t y d = d * M.P t d - M.c t * y - M.G t y d +
      ∫ ε : ℝ × ℝ, V (y - ε.1 * d - ε.2) ∂(M.μ t) := by
  have hh := hA.holding_integrable t ht y d hd
  have e1 : ∫ ε : ℝ × ℝ, (-M.h t (y - ε.1 * d - ε.2) + V (y - ε.1 * d - ε.2)) ∂(M.μ t) =
      (∫ ε : ℝ × ℝ, -M.h t (y - ε.1 * d - ε.2) ∂(M.μ t)) +
        ∫ ε : ℝ × ℝ, V (y - ε.1 * d - ε.2) ∂(M.μ t) := integral_add hh.neg (hint y d hd)
  unfold Model.gWith Model.G
  rw [e1, integral_neg]
  ring

theorem csl_gcont (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (V : ℝ → ℝ) (hVc : Continuous V) (C : ℝ) (hC : ∀ x, |V x| ≤ C * (1 + |x| ^ M.ρ)) :
    ContinuousOn (fun q : ℝ × ℝ => M.gWith V t q.1 q.2)
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) := by
  have hint : ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      Integrable (fun ε : ℝ × ℝ => V (y - ε.1 * d - ε.2)) (M.μ t) :=
    fun y d hd => csl_integrable_comp M hA t ht V hVc C hC y d hd
  have hV := csl_continuousOn_integral M hA t ht V hVc C hC
  have hG := csl_G_contOn M hA t ht
  have hrev : ContinuousOn (fun q : ℝ × ℝ => q.2 * M.P t q.2)
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) :=
    continuousOn_snd.mul ((hA.price_continuous t ht).comp continuousOn_snd (fun q hq => hq.2))
  have hlin : ContinuousOn (fun q : ℝ × ℝ => M.c t * q.1)
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) :=
    (continuous_const.mul continuous_fst).continuousOn
  refine (((hrev.sub hlin).sub hG).add hV).congr (fun q hq => ?_)
  exact csl_g_split M hA t ht V hint q.1 q.2 hq.2

theorem csl_g_upper (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (V : ℝ → ℝ) (hVc : Continuous V) (C : ℝ) (hC : ∀ x, |V x| ≤ C * (1 + |x| ^ M.ρ))
    (c' B : ℝ) (hVb : ∀ x, V x ≤ c' * x + B) (y d : ℝ) (hd : d ∈ Set.Icc (M.dlo t) (M.dhi t)) :
    M.gWith V t y d ≤ d * M.P t d - c' * d + B - ((M.c t - c') * y + M.G t y d) := by
  have := hA.law_probability t ht
  have hint : ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      Integrable (fun ε : ℝ × ℝ => V (y - ε.1 * d - ε.2)) (M.μ t) :=
    fun y d hd => csl_integrable_comp M hA t ht V hVc C hC y d hd
  rw [csl_g_split M hA t ht V hint y d hd]
  obtain ⟨hmi, hmv⟩ := csl_mean M hA t ht y d
  have hle : ∫ ε : ℝ × ℝ, V (y - ε.1 * d - ε.2) ∂(M.μ t) ≤
      ∫ ε : ℝ × ℝ, (c' * (y - ε.1 * d - ε.2) + B) ∂(M.μ t) :=
    integral_mono (hint y d hd) ((hmi.const_mul c').add (integrable_const B))
      (fun ε => hVb _)
  have hrhs : ∫ ε : ℝ × ℝ, (c' * (y - ε.1 * d - ε.2) + B) ∂(M.μ t) = c' * (y - d) + B := by
    rw [integral_add (hmi.const_mul c') (integrable_const B), integral_const_mul, hmv]
    simp
  rw [hrhs] at hle
  nlinarith [hle]

open Filter



/-- Auxiliary copy of the display of `v*_t`. -/
theorem vstar_display_aux (k : ℝ) (G : ℝ → ℝ) (hk : 0 ≤ k)
    (hGcont : Continuous G) (hGright : Tendsto G atTop atBot)
    (hGleft : Tendsto G atBot atBot)
    (hGsym : SymKConvex k (fun y => -G y))
    (S : ℝ) (hS : ∀ y, G y ≤ G S) :
    (∀ x, orderEnvelope k G x =
      if x ∈ {y | y ≤ S ∧ G y ≤ G S - k} then -k + G S else G x) ∧
    (∀ x, G x ≤ orderEnvelope k G x) ∧
    (∀ x ≤ S, -k + G S ≤ orderEnvelope k G x) := by
  have hδ0 : ∀ x : ℝ, δ (x - x) = 0 := fun x => by simp [δ]
  have hδ1 : ∀ x y : ℝ, x < y → δ (y - x) = 1 := fun x y h => by
    simp [δ, h]
  -- upper bound for elements
  have hub : ∀ x y : ℝ, x ≤ y → -k * δ (y - x) + G y ≤ G S := by
    intro x y _
    have h0 : 0 ≤ δ (y - x) := by unfold δ; split_ifs <;> norm_num
    nlinarith [hS y]
  have hbdd : ∀ x : ℝ, BddAbove ((fun y => -k * δ (y - x) + G y) '' Set.Ici x) := by
    intro x
    exact ⟨G S, by rintro _ ⟨y, hy, rfl⟩; exact hub x y hy⟩
  have hge_G : ∀ x, G x ≤ orderEnvelope k G x := by
    intro x
    apply le_csSup (hbdd x)
    exact ⟨x, Set.mem_Ici.mpr le_rfl, by show -k * δ (x - x) + G x = G x; rw [hδ0]; ring⟩
  have hge_S : ∀ x ≤ S, -k + G S ≤ orderEnvelope k G x := by
    intro x hx
    rcases eq_or_lt_of_le hx with h | h
    · rw [h]
      have := hge_G S
      linarith
    · apply le_csSup (hbdd x)
      refine ⟨S, Set.mem_Ici.mpr hx, ?_⟩
      simp [hδ1 x S h]
  refine ⟨?_, hge_G, hge_S⟩
  intro x
  by_cases hx : x ∈ {y | y ≤ S ∧ G y ≤ G S - k}
  · rw [if_pos hx]
    have hxS : x ≤ S := hx.1
    have hGx : G x ≤ G S - k := hx.2
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, x, Set.mem_Ici.mpr le_rfl, rfl⟩
      · rintro _ ⟨y, hy, rfl⟩
        dsimp only
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with h | h
        · rw [← h, hδ0]; linarith
        · rw [hδ1 x y h]; linarith [hS y]
    · exact hge_S x hxS
  · rw [if_neg hx]
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, x, Set.mem_Ici.mpr le_rfl, rfl⟩
      · rintro _ ⟨y, hy, rfl⟩
        dsimp only
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with h | h
        · rw [← h, hδ0]; linarith
        · rw [hδ1 x y h]
          -- need G y - k ≤ G x
          have hcase : G S - k < G x ∨ S < x := by
            by_contra hcon
            push_neg at hcon
            exact hx ⟨hcon.2, hcon.1⟩
          rcases hcase with hc | hc
          · linarith [hS y]
          · -- S < x < y: sym-k-concavity of G
            have hxy : x < y := h
            have hSy : 0 < y - S := by linarith
            set l : ℝ := (x - S) / (y - S) with hl
            have hl0 : 0 ≤ l := div_nonneg (by linarith) hSy.le
            have hl1 : l ≤ 1 := by rw [hl, div_le_one hSy]; linarith
            have hxeq : x = (1 - l) * S + l * y := by
              rw [hl]; field_simp; ring
            have := hGsym S y l ⟨hl0, hl1⟩
            try simp only at this
            rw [← hxeq] at this
            have hm : max l (1 - l) ≤ 1 := max_le hl1 (by linarith)
            have h1l : 0 ≤ 1 - l := by linarith
            nlinarith [mul_le_mul_of_nonneg_right hm hk, mul_le_mul_of_nonneg_left (hS y) h1l]
    · exact hge_G x

/-- Cases 1–4 in the proof of Theorem 4.1, p. 892. -/
theorem csl_v_sym_concave (k : ℝ) (G : ℝ → ℝ) (hk : 0 ≤ k)
    (hGcont : Continuous G) (hGright : Tendsto G atTop atBot)
    (hGleft : Tendsto G atBot atBot)
    (hGsym : SymKConvex k (fun y => -G y)) (c : ℝ) :
    SymKConvex k (fun x => -(c * x + orderEnvelope k G x)) := by
  -- a global maximizer
  have hco : Tendsto (fun y => -G y) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact (tendsto_neg_atBot_atTop.comp hGleft).sup (tendsto_neg_atBot_atTop.comp hGright)
  obtain ⟨S, hS'⟩ := (hGcont.neg).exists_forall_le hco
  have hS : ∀ y, G y ≤ G S := fun y => by simpa using hS' y
  obtain ⟨hform, hge, hflat⟩ := vstar_display_aux k G hk hGcont hGright hGleft hGsym S hS
  set u := orderEnvelope k G with hu
  have hdich : ∀ x, u x = G x ∨ (x ≤ S ∧ u x = G S - k) := by
    intro x
    rw [hform x]
    by_cases hx : x ∈ {y | y ≤ S ∧ G y ≤ G S - k}
    · rw [if_pos hx]; right; exact ⟨hx.1, by ring⟩
    · rw [if_neg hx]; left; rfl
  have hle : ∀ x, u x ≤ G S := by
    intro x
    rcases hdich x with h | h
    · rw [h]; exact hS x
    · rw [h.2]; linarith
  -- the mixed case
  have mixed : ∀ x0 x1 l : ℝ, x0 ≤ S → u x0 = G S - k → u x1 = G x1 → 0 ≤ l → l ≤ 1 →
      (1 - l) * u x0 + l * u x1 - max l (1 - l) * k ≤ u ((1 - l) * x0 + l * x1) := by
    intro x0 x1 l hx0 hu0 hu1 hl0 hl1
    have hL : l ≤ max l (1 - l) := le_max_left _ _
    have hL1 : max l (1 - l) ≤ 1 := max_le hl1 (by linarith)
    have hL0 : 0 ≤ max l (1 - l) := le_trans hl0 hL
    set xl := (1 - l) * x0 + l * x1 with hxl
    by_cases hxS : xl ≤ S
    · have h1 := hflat xl hxS
      have h2 := hS x1
      rw [hu0, hu1]
      nlinarith [mul_le_mul_of_nonneg_right hL hk, mul_le_mul_of_nonneg_left h2 hl0]
    · push_neg at hxS
      have hx1 : S < x1 := by
        by_contra hcon
        push_neg at hcon
        have : xl ≤ S := by
          rw [hxl]; nlinarith
        linarith
      have hSy : 0 < x1 - S := by linarith
      set m : ℝ := (xl - S) / (x1 - S) with hm
      have hm0 : 0 ≤ m := div_nonneg (by linarith) hSy.le
      have hxl_le : xl ≤ x1 := by rw [hxl]; nlinarith
      have hm1 : m ≤ 1 := by rw [hm, div_le_one hSy]; linarith
      have hmeq : xl = (1 - m) * S + m * x1 := by
        rw [hm]; field_simp; ring
      have hml : m ≤ l := by
        rw [hm, div_le_iff₀ hSy, hxl]
        nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hx0)]
      have hsym := hGsym S x1 m ⟨hm0, hm1⟩
      try simp only at hsym
      rw [← hmeq] at hsym
      have hM1 : max m (1 - m) ≤ 1 := max_le hm1 (by linarith)
      have hGxl : G xl ≤ u xl := hge xl
      have h2 := hS x1
      rw [hu0, hu1]
      have e1 : 0 ≤ (l - m) * (G S - G x1) := mul_nonneg (by linarith) (by linarith)
      have e2 : 0 ≤ k * ((1 - l) + max l (1 - l) - max m (1 - m)) :=
        mul_nonneg hk (by linarith)
      nlinarith [e1, e2]
  intro x0 x1 l hl
  obtain ⟨hl0, hl1⟩ := hl
  try simp only
  have hkey : (1 - l) * u x0 + l * u x1 - max l (1 - l) * k ≤ u ((1 - l) * x0 + l * x1) := by
    rcases hdich x0 with h0 | h0 <;> rcases hdich x1 with h1 | h1
    · have := hGsym x0 x1 l ⟨hl0, hl1⟩
      try simp only at this
      have := hge ((1 - l) * x0 + l * x1)
      rw [h0, h1]
      nlinarith
    · -- x0 in G-region, x1 flat
      have := mixed x1 x0 (1 - l) h1.1 h1.2 h0 (by linarith) (by linarith)
      have e : (1 - (1 - l)) * x1 + (1 - l) * x0 = (1 - l) * x0 + l * x1 := by ring
      have e2 : max (1 - l) (1 - (1 - l)) = max l (1 - l) := by rw [sub_sub_cancel, max_comm]
      rw [e, e2] at this
      linarith
    · exact mixed x0 x1 l h0.1 h0.2 h1 hl0 hl1
    · have hx1S := h1.1
      have hxlS : (1 - l) * x0 + l * x1 ≤ S := by nlinarith [h0.1]
      have := hflat _ hxlS
      rw [h0.2, h1.2]
      have : 0 ≤ max l (1 - l) * k := mul_nonneg (le_trans hl0 (le_max_left _ _)) hk
      nlinarith
  have e : c * ((1 - l) * x0 + l * x1) = (1 - l) * (c * x0) + l * (c * x1) := by ring
  nlinarith [hkey, e]




/-- Lemma 5(d), p. 891. -/
theorem csl_lemma_5_d (k : ℝ) (g : ℝ → ℝ) (hk : 0 ≤ k)
    (hg : SymKConvex k g) (hcont : Continuous g)
    (h₁ : Tendsto g atTop atTop) (h₂ : Tendsto g atBot atTop) :
    ∃ s S : ℝ, s ≤ S ∧ (∀ y, g S ≤ g y) ∧
      IsLeast {x | g x = g S + k} s ∧
      (∀ y < s, g s < g y) ∧
      ∀ y z, (s + S) / 2 ≤ y → y ≤ z → g y ≤ g z + k := by
  -- a global minimizer
  have hco : Tendsto g (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]; exact h₂.sup h₁
  obtain ⟨S, hS⟩ := hcont.exists_forall_le hco
  -- far-left strict bound
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ b ≤ a, g S + k < g b :=
    eventually_atBot.mp (h₂.eventually (eventually_gt_atTop (g S + k)))
  -- a point left of S at level gS + k
  have hx0 : ∃ x0 ≤ S, g x0 = g S + k := by
    have hab : min a S ≤ S := min_le_right _ _
    have h1 : g S + k < g (min a S) := ha _ (min_le_left _ _)
    have := intermediate_value_Icc' hab hcont.continuousOn
      (show g S + k ∈ Set.Icc (g S) (g (min a S)) from ⟨by linarith, h1.le⟩)
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨x, hx.2, hxe⟩
  obtain ⟨x0, hx0S, hx0e⟩ := hx0
  -- least point of the level set
  have hleast : ∃ s, IsLeast {x | g x = g S + k} s := by
    have hcpt : IsCompact ({x | g x = g S + k} ∩ Set.Icc (min a x0) x0) :=
      isCompact_Icc.inter_left (isClosed_eq hcont continuous_const)
    have hne : ({x | g x = g S + k} ∩ Set.Icc (min a x0) x0).Nonempty :=
      ⟨x0, hx0e, min_le_right _ _, le_refl _⟩
    obtain ⟨s, hs⟩ := hcpt.exists_isLeast hne
    refine ⟨s, hs.1.1, fun x hx => ?_⟩
    by_cases hxx : x ≤ x0
    · have hmin : min a x0 ≤ x := by
        by_contra hlt
        push_neg at hlt
        have := ha x ((lt_of_lt_of_le hlt (min_le_left _ _)).le)
        rw [hx] at this
        exact lt_irrefl _ this
      exact hs.2 ⟨hx, hmin, hxx⟩
    · push_neg at hxx
      exact le_trans (hs.2 ⟨hx0e, min_le_right _ _, le_refl _⟩) hxx.le
  obtain ⟨s, hs⟩ := hleast
  have hsx0 : s ≤ x0 := hs.2 hx0e
  have hsS : s ≤ S := le_trans hsx0 hx0S
  have hgs : g s = g S + k := hs.1
  refine ⟨s, S, hsS, hS, hs, ?_, ?_⟩
  · intro y hy
    by_contra hnot
    push_neg at hnot
    have hne : g y ≠ g S + k := fun h => absurd (hs.2 h) (not_le.mpr hy)
    have hlt : g y < g S + k := lt_of_le_of_ne (by rw [← hgs]; exact hnot) hne
    have hab : min a y ≤ y := min_le_right _ _
    have h1 : g S + k < g (min a y) := ha _ (min_le_left _ _)
    obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc' hab hcont.continuousOn
      (show g S + k ∈ Set.Icc (g y) (g (min a y)) from ⟨hlt.le, h1.le⟩)
    have := hs.2 hxe
    linarith [hx.2]
  · intro y z hy hyz
    by_cases hyS : S ≤ y
    · -- y between S and z
      rcases eq_or_lt_of_le hyS with h | h
      · rw [← h]; linarith [hS z]
      · have hSz : S < z := lt_of_lt_of_le h hyz
        set l : ℝ := (y - S) / (z - S) with hl
        have hzS : 0 < z - S := by linarith
        have hl0 : 0 ≤ l := div_nonneg (by linarith) hzS.le
        have hl1 : l ≤ 1 := by rw [hl, div_le_one hzS]; linarith
        have hyeq : y = (1 - l) * S + l * z := by
          rw [hl]; field_simp; ring
        have := hg S z l ⟨hl0, hl1⟩
        rw [← hyeq] at this
        have hm : max l (1 - l) ≤ 1 := max_le hl1 (by linarith)
        have hgS := hS z
        have h1l : 0 ≤ 1 - l := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hm hk, mul_le_mul_of_nonneg_left hgS h1l]
    · push_neg at hyS
      -- y in [(s+S)/2, S)
      have hsy : s < y := by linarith
      have hSs : 0 < S - s := by linarith
      set l : ℝ := (y - s) / (S - s) with hl
      have hl0 : 0 ≤ l := div_nonneg (by linarith) hSs.le
      have hl1 : l ≤ 1 := by rw [hl, div_le_one hSs]; linarith
      have hlh : 1 / 2 ≤ l := by
        rw [hl, le_div_iff₀ hSs]; linarith
      have hyeq : y = (1 - l) * s + l * S := by
        rw [hl]; field_simp; ring
      have := hg s S l ⟨hl0, hl1⟩
      rw [← hyeq, hgs] at this
      have hmax : max l (1 - l) = l := max_eq_left (by linarith)
      rw [hmax] at this
      nlinarith [hS z, this]

theorem csl_convex_affine_add (a : ℝ) (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun y => a * y + f y) := by
  refine ⟨convex_univ, fun y0 _ y1 _ s u hs hu hsu => ?_⟩
  have := hf.2 (Set.mem_univ y0) (Set.mem_univ y1) hs hu hsu
  simp only [smul_eq_mul] at this ⊢
  have e : a * (s * y0 + u * y1) = s * (a * y0) + u * (a * y1) := by ring
  rw [e]
  linarith

theorem csl_convex_comp_neg (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun y => f (-y)) := by
  refine ⟨convex_univ, fun y0 _ y1 _ s u hs hu hsu => ?_⟩
  have := hf.2 (Set.mem_univ (-y0)) (Set.mem_univ (-y1)) hs hu hsu
  simp only [smul_eq_mul] at this ⊢
  have e : -(s * y0 + u * y1) = s * (-y0) + u * (-y1) := by ring
  rw [e]
  exact this

theorem csl_g_unif_neg (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (V : ℝ → ℝ) (hVc : Continuous V) (C : ℝ) (hC : ∀ x, |V x| ≤ C * (1 + |x| ^ M.ρ))
    (B : ℝ) (hVb : ∀ x, V x ≤ M.c (t + 1) * x + B) (L : ℝ) :
    ∃ Y : ℝ, ∀ y, Y ≤ |y| → ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t), M.gWith V t y d ≤ -L := by
  set c' := M.c (t + 1) with hc'def
  have hc' : 0 ≤ c' := csl_c_nonneg M hA t ht
  have hKb : ∃ K : ℝ, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t), d * M.P t d - c' * d + B ≤ K := by
    have hc : ContinuousOn (fun d => d * M.P t d - c' * d + B) (Set.Icc (M.dlo t) (M.dhi t)) :=
      ((continuousOn_id.mul (hA.price_continuous t ht)).sub
        (continuousOn_const.mul continuousOn_id)).add continuousOn_const
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    exact ⟨K, fun d hd => le_trans (le_abs_self _) (by simpa using hK d hd)⟩
  obtain ⟨K, hKd⟩ := hKb
  have hGc := csl_G_contOn M hA t ht
  have hGy : ∀ y, ContinuousOn (fun d => M.G t y d) (Set.Icc (M.dlo t) (M.dhi t)) := fun y =>
    hGc.comp (continuousOn_const.prodMk continuousOn_id) (fun d hd => ⟨Set.mem_univ _, hd⟩)
  obtain ⟨Y1, hY1⟩ := csl_unif_coercive (fun y d => (M.c t - c') * y + M.G t y d)
    (M.dlo t) (M.dhi t)
    (fun d hd => csl_convex_affine_add _ _ (csl_G_convex_y M hA t ht d hd))
    (fun y => continuousOn_const.add (hGy y))
    (fun d hd => hA.holding_right t ht d hd) (K + L)
  obtain ⟨Y2, hY2⟩ := csl_unif_coercive (fun y d => M.c t * (-y) + M.G t (-y) d)
    (M.dlo t) (M.dhi t)
    (fun d hd => csl_convex_comp_neg _
      (csl_convex_affine_add (M.c t) _ (csl_G_convex_y M hA t ht d hd)))
    (fun y => continuousOn_const.add (hGy (-y)))
    (fun d hd => (hA.holding_left t ht d hd).comp tendsto_neg_atTop_atBot) (K + L)
  refine ⟨max Y1 Y2, fun y hy d hd => ?_⟩
  have hup := csl_g_upper M hA t ht V hVc C hC c' B hVb y d hd
  have hK := hKd d hd
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h] at hy
    have := hY1 y (le_trans (le_max_left _ _) hy) d hd
    try simp only at this
    linarith
  · rw [abs_of_nonpos h] at hy
    have := hY2 (-y) (le_trans (le_max_right _ _) hy) d hd
    simp only [neg_neg] at this
    have hcy : c' * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc' h
    nlinarith

theorem csl_gstar_facts (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (V : ℝ → ℝ) (hVc : Continuous V) (C : ℝ) (hC : ∀ x, |V x| ≤ C * (1 + |x| ^ M.ρ))
    (B : ℝ) (hVb : ∀ x, V x ≤ M.c (t + 1) * x + B) :
    Continuous (M.GstarWith V t) ∧ Tendsto (M.GstarWith V t) atTop atBot ∧
    Tendsto (M.GstarWith V t) atBot atBot ∧
    ∀ y, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      (∀ e ∈ Set.Icc (M.dlo t) (M.dhi t), M.gWith V t y e ≤ M.gWith V t y d) ∧
      M.GstarWith V t y = M.gWith V t y d := by
  have hpq := hA.demand_interval t ht
  have hgcont := csl_gcont M hA t ht V hVc C hC
  have hatt := csl_gstar_attain M t V hpq hgcont
  refine ⟨?_, ?_, ?_, hatt⟩
  · haveI : CompactSpace (Set.Icc (M.dlo t) (M.dhi t)) := isCompact_iff_compactSpace.mp isCompact_Icc
    have hfc : Continuous (fun x : ℝ × Set.Icc (M.dlo t) (M.dhi t) => M.gWith V t x.1 x.2.1) :=
      hgcont.comp_continuous (f := fun x : ℝ × Set.Icc (M.dlo t) (M.dhi t) => (x.1, (x.2 : ℝ)))
        (by fun_prop) (fun x => ⟨Set.mem_univ _, x.2.2⟩)
    have := (isCompact_univ (X := Set.Icc (M.dlo t) (M.dhi t))).continuous_sSup
      (f := fun (y : ℝ) (e : Set.Icc (M.dlo t) (M.dhi t)) => M.gWith V t y e) hfc
    convert this using 2 with y
    unfold Model.GstarWith
    congr 1
    ext z
    constructor
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨⟨e, he⟩, -, rfl⟩; exact ⟨e, he, rfl⟩
  · rw [tendsto_atBot]
    intro b
    obtain ⟨Y, hY⟩ := csl_g_unif_neg M hA t ht V hVc C hC B hVb (-b)
    filter_upwards [eventually_ge_atTop (max Y 0)] with y hy
    obtain ⟨d, hd, -, he⟩ := hatt y
    rw [he]
    have h0 : 0 ≤ y := le_trans (le_max_right _ _) hy
    have := hY y (by rw [abs_of_nonneg h0]; exact le_trans (le_max_left _ _) hy) d hd
    linarith
  · rw [tendsto_atBot]
    intro b
    obtain ⟨Y, hY⟩ := csl_g_unif_neg M hA t ht V hVc C hC B hVb (-b)
    filter_upwards [eventually_le_atBot (-(max Y 0))] with y hy
    obtain ⟨d, hd, -, he⟩ := hatt y
    rw [he]
    have h0 : y ≤ 0 := by have := le_max_right Y 0; linarith
    have := hY y (by rw [abs_of_nonpos h0]; have := le_max_left Y 0; linarith) d hd
    linarith

/-! ### Section G: the downward induction -/

def CslInv (M : Model) (t : ℕ) : Prop :=
  Continuous (M.v t) ∧ SymKConvex M.k (fun x => -M.v t x) ∧
  (∃ C : ℝ, ∀ x, |M.v t x| ≤ C * (1 + |x| ^ M.ρ)) ∧ (∃ B : ℝ, ∀ x, M.v t x ≤ M.c t * x + B)

def CslPeriod (M : Model) (t : ℕ) : Prop :=
  (∃ C : ℝ, ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t), |M.g t y d| ≤ C * (1 + |y| ^ M.ρ)) ∧
  ContinuousOn (fun q : ℝ × ℝ => M.g t q.1 q.2) (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) ∧
  (∀ d ∈ Set.Icc (M.dlo t) (M.dhi t), Tendsto (fun y => M.g t y d) (cocompact ℝ) atBot) ∧
  (∀ y, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t), ∀ e ∈ Set.Icc (M.dlo t) (M.dhi t),
      M.g t y e ≤ M.g t y d) ∧
  (∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      Integrable (fun ε : ℝ × ℝ => M.v (t + 1) (y - ε.1 * d - ε.2)) (M.μ t)) ∧
  SymKConvex M.k (fun y => -M.Gstar t y) ∧ Continuous (M.Gstar t) ∧
  Tendsto (M.Gstar t) atTop atBot ∧ Tendsto (M.Gstar t) atBot atBot ∧
  (∀ y, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t), M.Gstar t y = M.g t y d)

theorem csl_v_top (M : Model) : M.v (M.T + 1) = fun _ => 0 := by
  unfold Model.v
  simp [Model.vAux]

theorem csl_inv_top (M : Model) (hA : M.Assumptions) : CslInv M (M.T + 1) := by
  rw [CslInv, csl_v_top]
  refine ⟨continuous_const, ?_, ⟨0, by simp⟩, ⟨0, ?_⟩⟩
  · intro x0 x1 l hl
    simp only [neg_zero, mul_zero, add_zero, zero_add]
    exact mul_nonneg (le_trans hl.1 (le_max_left _ _)) hA.fixed_nonneg
  · intro x
    rw [hA.terminal_unit]
    simp

theorem csl_vformula (M : Model) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (x : ℝ) :
    M.v t x = M.c t * x + orderEnvelope M.k (M.Gstar t) x := by
  rw [Finset.mem_Icc] at ht
  obtain ⟨n, hn⟩ : ∃ n, M.T + 1 - t = n + 1 := ⟨M.T - t, by omega⟩
  have hv : M.v (t + 1) = M.vAux n := by
    unfold Model.v; congr 1; omega
  have htn : M.T - n = t := by omega
  have h1 : M.v t x = M.c t * x + sSup ((M.orderObj t x) '' Set.Ici x) := by
    show M.vAux (M.T + 1 - t) x = _
    rw [hn, Model.vAux, htn, Model.orderObj, hv]
  rw [h1]
  rfl

theorem csl_step (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (hInv : CslInv M (t + 1)) : CslPeriod M t ∧ CslInv M t := by
  obtain ⟨hVc, hVsym, ⟨C, hC⟩, ⟨B, hVb⟩⟩ := hInv
  have hpq := hA.demand_interval t ht
  have hrho := csl_rho_pos M hA
  have hint : ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      Integrable (fun ε : ℝ × ℝ => M.v (t + 1) (y - ε.1 * d - ε.2)) (M.μ t) :=
    fun y d hd => csl_integrable_comp M hA t ht (M.v (t + 1)) hVc C hC y d hd
  have hgcont : ContinuousOn (fun q : ℝ × ℝ => M.g t q.1 q.2)
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) := csl_gcont M hA t ht _ hVc C hC
  obtain ⟨hGc, hGtop, hGbot, hatt⟩ := csl_gstar_facts M hA t ht (M.v (t + 1)) hVc C hC B hVb
  have hsym : SymKConvex M.k (fun y => -M.Gstar t y) :=
    csl_sym_gstar_step M hA t ht (M.v (t + 1)) hVc hVsym ⟨C, hC⟩ hgcont
  -- growth of g
  have hgrowth : ∃ C' : ℝ, ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      |M.g t y d| ≤ C' * (1 + |y| ^ M.ρ) := by
    obtain ⟨Cg, hCg⟩ := hA.holding_growth t ht
    obtain ⟨C2, hC2⟩ := csl_integral_poly_bound M hA t ht (M.v (t + 1)) hVc C hC
    obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t), |d * M.P t d| ≤ K1 := by
      have hc : ContinuousOn (fun d => d * M.P t d) (Set.Icc (M.dlo t) (M.dhi t)) :=
        continuousOn_id.mul (hA.price_continuous t ht)
      obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
      exact ⟨K, fun d hd => by simpa using hK d hd⟩
    refine ⟨|K1| + |M.c t| + |Cg| + |C2|, fun y d hd => ?_⟩
    have hs0 : 0 ≤ |y| ^ M.ρ := by positivity
    have hy : |y| ≤ 1 + |y| ^ M.ρ := by
      rcases le_total |y| 1 with h | h
      · linarith
      · have := le_self_pow₀ h (show M.ρ ≠ 0 by omega)
        linarith
    have h1 : |d * M.P t d| ≤ |K1| * (1 + |y| ^ M.ρ) :=
      le_trans (hK1 d hd) (le_trans (le_abs_self K1)
        (le_mul_of_one_le_right (abs_nonneg _) (by linarith)))
    have h2 : |M.c t * y| ≤ |M.c t| * (1 + |y| ^ M.ρ) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    have hG0 := hA.holding_nonneg t ht y d hd
    have h3 : |M.G t y d| ≤ |Cg| * (1 + |y| ^ M.ρ) := by
      rw [abs_of_nonneg hG0]
      exact le_trans (hCg y d hd) (mul_le_mul_of_nonneg_right (le_abs_self Cg) (by linarith))
    have h4 : |∫ ε : ℝ × ℝ, M.v (t + 1) (y - ε.1 * d - ε.2) ∂(M.μ t)| ≤ |C2| * (1 + |y| ^ M.ρ) :=
      le_trans (hC2 y d hd) (mul_le_mul_of_nonneg_right (le_abs_self C2) (by linarith))
    have hsplit := csl_g_split M hA t ht (M.v (t + 1)) hint y d hd
    have hgdef : M.g t y d = M.gWith (M.v (t + 1)) t y d := rfl
    rw [hgdef, hsplit]
    have a1 := abs_add_le (d * M.P t d - M.c t * y - M.G t y d)
      (∫ ε : ℝ × ℝ, M.v (t + 1) (y - ε.1 * d - ε.2) ∂(M.μ t))
    have a2 := abs_sub (d * M.P t d - M.c t * y) (M.G t y d)
    have a3 := abs_sub (d * M.P t d) (M.c t * y)
    nlinarith
  have hb2 : ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      Tendsto (fun y => M.g t y d) (cocompact ℝ) atBot := by
    intro d hd
    rw [tendsto_atBot, cocompact_eq_atBot_atTop]
    intro b
    obtain ⟨Y, hY⟩ := csl_g_unif_neg M hA t ht (M.v (t + 1)) hVc C hC B hVb (-b)
    rw [Filter.eventually_sup]
    constructor
    · filter_upwards [eventually_le_atBot (-(max Y 0))] with y hy
      have h0 : y ≤ 0 := by have := le_max_right Y 0; linarith
      have := hY y (by rw [abs_of_nonpos h0]; have := le_max_left Y 0; linarith) d hd
      show M.gWith (M.v (t + 1)) t y d ≤ b
      linarith
    · filter_upwards [eventually_ge_atTop (max Y 0)] with y hy
      have h0 : 0 ≤ y := le_trans (le_max_right _ _) hy
      have := hY y (by rw [abs_of_nonneg h0]; exact le_trans (le_max_left _ _) hy) d hd
      show M.gWith (M.v (t + 1)) t y d ≤ b
      linarith
  have hb3 : ∀ y, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t), ∀ e ∈ Set.Icc (M.dlo t) (M.dhi t),
      M.g t y e ≤ M.g t y d := fun y => by
    obtain ⟨d, hd, hmax, -⟩ := hatt y
    exact ⟨d, hd, hmax⟩
  have hatt' : ∀ y, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t), M.Gstar t y = M.g t y d := fun y => by
    obtain ⟨d, hd, -, he⟩ := hatt y
    exact ⟨d, hd, he⟩
  refine ⟨⟨hgrowth, hgcont, hb2, hb3, hint, hsym, hGc, hGtop, hGbot, hatt'⟩, ?_⟩
  -- the invariant at t
  have hk := hA.fixed_nonneg
  have hco : Tendsto (fun y => -M.Gstar t y) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact (tendsto_neg_atBot_atTop.comp hGbot).sup (tendsto_neg_atBot_atTop.comp hGtop)
  obtain ⟨S, hS'⟩ := (hGc.neg).exists_forall_le hco
  have hS : ∀ y, M.Gstar t y ≤ M.Gstar t S := fun y => neg_le_neg_iff.1 (hS' y)
  obtain ⟨hform, hge, hflat⟩ := vstar_display_aux M.k (M.Gstar t) hk hGc hGtop hGbot hsym S hS
  have hv := csl_vformula M t ht
  have hEle : ∀ x, orderEnvelope M.k (M.Gstar t) x ≤ M.Gstar t S := by
    intro x
    rw [hform x]
    split_ifs with h
    · linarith
    · exact hS x
  have hEc : Continuous (orderEnvelope M.k (M.Gstar t)) := by
    have e : orderEnvelope M.k (M.Gstar t) =
        fun x => if x ≤ S then max (M.Gstar t x) (M.Gstar t S - M.k) else M.Gstar t x := by
      funext x
      rw [hform x]
      by_cases hx : x ≤ S
      · rw [if_pos hx]
        by_cases hg : M.Gstar t x ≤ M.Gstar t S - M.k
        · rw [if_pos ⟨hx, hg⟩, max_eq_right hg]; ring
        · rw [if_neg (fun h => hg h.2), max_eq_left (not_le.1 hg).le]
      · rw [if_neg hx, if_neg (fun h => hx h.1)]
    rw [e]
    exact Continuous.if_le (hGc.max continuous_const) hGc continuous_id continuous_const
      (fun x hx => by
        have hx' : x = S := hx
        rw [hx']; exact max_eq_left (by linarith))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : M.v t = fun x => M.c t * x + orderEnvelope M.k (M.Gstar t) x := funext (hv)
    rw [this]
    exact (continuous_const.mul continuous_id).add hEc
  · have h := csl_v_sym_concave M.k (M.Gstar t) hk hGc hGtop hGbot hsym (M.c t)
    have e : (fun x => -M.v t x) =
        fun x => -(M.c t * x + orderEnvelope M.k (M.Gstar t) x) := funext fun x => by rw [hv x]
    rw [e]; exact h
  · obtain ⟨Cg, hCg⟩ := hgrowth
    have hd0 : M.dlo t ∈ Set.Icc (M.dlo t) (M.dhi t) := ⟨le_rfl, hpq⟩
    refine ⟨|M.c t| + |M.Gstar t S| + |Cg|, fun x => ?_⟩
    have hs0 : 0 ≤ |x| ^ M.ρ := by positivity
    have hy : |x| ≤ 1 + |x| ^ M.ρ := by
      rcases le_total |x| 1 with h | h
      · linarith
      · have := le_self_pow₀ h (show M.ρ ≠ 0 by omega)
        linarith
    have hcx : |M.c t * x| ≤ |M.c t| * (1 + |x| ^ M.ρ) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    have hup := hEle x
    have hlow : M.g t x (M.dlo t) ≤ orderEnvelope M.k (M.Gstar t) x := by
      obtain ⟨d, hd, hmax, he⟩ := hatt x
      have h1 : M.g t x (M.dlo t) ≤ M.Gstar t x := le_of_le_of_eq (hmax _ hd0) he.symm
      exact h1.trans (hge x)
    have hg1 := (abs_le.1 (hCg x (M.dlo t) hd0)).1
    have hcl := (abs_le.1 hcx).1
    have hcu := (abs_le.1 hcx).2
    have hGS : M.Gstar t S ≤ |M.Gstar t S| := le_abs_self _
    have hGS' : 0 ≤ |M.Gstar t S| := abs_nonneg _
    rw [hv x, abs_le]
    have hCgn : Cg * (1 + |x| ^ M.ρ) ≤ |Cg| * (1 + |x| ^ M.ρ) :=
      mul_le_mul_of_nonneg_right (le_abs_self Cg) (by linarith)
    have hGS2 : |M.Gstar t S| ≤ |M.Gstar t S| * (1 + |x| ^ M.ρ) :=
      le_mul_of_one_le_right hGS' (by linarith)
    have hCg0 : 0 ≤ |Cg| * (1 + |x| ^ M.ρ) := mul_nonneg (abs_nonneg Cg) (by linarith)
    have hexp : (|M.c t| + |M.Gstar t S| + |Cg|) * (1 + |x| ^ M.ρ) =
        |M.c t| * (1 + |x| ^ M.ρ) + |M.Gstar t S| * (1 + |x| ^ M.ρ) +
          |Cg| * (1 + |x| ^ M.ρ) := by ring
    rw [hexp]
    constructor
    · linarith
    · linarith
  · refine ⟨M.Gstar t S, fun x => ?_⟩
    rw [hv x]
    linarith [hEle x]

/-! ### Section H: induction and the three theorems -/

theorem csl_all (M : Model) (hA : M.Assumptions) :
    ∀ n, n ≤ M.T → CslInv M (M.T + 1 - n) := by
  intro n
  induction n with
  | zero => intro _; simpa using csl_inv_top M hA
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    have ht : M.T + 1 - (n + 1) ∈ Finset.Icc 1 M.T := by rw [Finset.mem_Icc]; omega
    have hInv : CslInv M (M.T + 1 - (n + 1) + 1) := by
      have : M.T + 1 - (n + 1) + 1 = M.T + 1 - n := by omega
      rw [this]; exact ih'
    exact (csl_step M hA _ ht hInv).2

theorem csl_period (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) :
    CslPeriod M t ∧ CslInv M t := by
  rw [Finset.mem_Icc] at ht
  have h := csl_all M hA (M.T - t) (by omega)
  have e : M.T + 1 - (M.T - t) = t + 1 := by omega
  rw [e] at h
  exact csl_step M hA t (Finset.mem_Icc.2 ht) h

theorem csl_thm_a (M : Model) (hA : M.Assumptions) :
    ∀ t ∈ Finset.Icc 1 M.T,
      (∃ C : ℝ, ∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        |M.g t y d| ≤ C * (1 + |y| ^ M.ρ)) ∧
      (∃ C : ℝ, ∀ x, |M.v t x| ≤ C * (1 + |x| ^ M.ρ)) ∧
      (∀ y, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        Integrable (fun ε : ℝ × ℝ => M.v (t + 1) (y - ε.1 * d - ε.2)) (M.μ t)) := by
  intro t ht
  obtain ⟨hP, hI⟩ := csl_period M hA t ht
  exact ⟨hP.1, hI.2.2.1, hP.2.2.2.2.1⟩

theorem csl_thm_b (M : Model) (hA : M.Assumptions) :
    ∀ t ∈ Finset.Icc 1 M.T,
      ContinuousOn (fun q : ℝ × ℝ => M.g t q.1 q.2)
        (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) ∧
      (∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        Tendsto (fun y => M.g t y d) (cocompact ℝ) atBot) ∧
      (∀ y, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) d) := by
  intro t ht
  obtain ⟨hP, hI⟩ := csl_period M hA t ht
  refine ⟨hP.2.1, hP.2.2.1, fun y => ?_⟩
  obtain ⟨d, hd, hmax⟩ := hP.2.2.2.1 y
  exact ⟨d, hd, isMaxOn_iff.2 hmax⟩

/-! ### Section I: the policy structure -/

theorem csl_policy (M : Model) (hA : M.Assumptions) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T)
    (hP : CslPeriod M t) :
    ∃ (s S : ℝ) (A : Set ℝ) (dsel : ℝ → ℝ),
        s ≤ S ∧ A ⊆ Set.Icc s ((s + S) / 2) ∧
        (∀ y : ℝ, dsel y ∈ Set.Icc (M.dlo t) (M.dhi t) ∧
          IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) (dsel y)) ∧
        ∀ x : ℝ,
          x ≤ sSAOrder s S A x ∧
          (∀ y, x ≤ y →
            M.orderObj t x y ≤ M.orderObj t x (sSAOrder s S A x)) ∧
          M.v t x = M.c t * x + M.orderObj t x (sSAOrder s S A x) := by
  obtain ⟨-, -, -, hb3, -, hsym, hGc, hGtop, hGbot, -⟩ := hP
  have hk := hA.fixed_nonneg
  obtain ⟨s, S, hsS, hSmin, hsleast, hsleft, hright⟩ :=
    csl_lemma_5_d M.k (fun y => -M.Gstar t y) hk hsym hGc.neg
      (tendsto_neg_atBot_atTop.comp hGtop) (tendsto_neg_atBot_atTop.comp hGbot)
  have hSmax : ∀ y, M.Gstar t y ≤ M.Gstar t S := fun y => by
    have := hSmin y; linarith
  have hs_eq : M.Gstar t s = M.Gstar t S - M.k := by
    have h2 : -M.Gstar t s = -M.Gstar t S + M.k := hsleast.1
    linarith
  have hs_left : ∀ y, y < s → M.Gstar t y < M.Gstar t s := fun y hy => by
    have := hsleft y hy; linarith
  have hright' : ∀ y z, (s + S) / 2 ≤ y → y ≤ z → M.Gstar t z ≤ M.Gstar t y + M.k := by
    intro y z h1 h2
    have := hright y z h1 h2
    linarith
  choose dsel hdsel1 hdsel2 using hb3
  set A : Set ℝ := {x | x ∈ Set.Icc s ((s + S) / 2) ∧ M.Gstar t x < M.Gstar t S - M.k} with hAdef
  have hδ0 : ∀ x : ℝ, δ (x - x) = 0 := fun x => by simp [δ]
  have hδ1 : ∀ x y : ℝ, x < y → δ (y - x) = 1 := fun x y h => by simp [δ, h]
  have hmain : ∀ x, x ≤ sSAOrder s S A x ∧ ∀ y, x ≤ y →
      -M.k * δ (y - x) + M.Gstar t y ≤
        -M.k * δ (sSAOrder s S A x - x) + M.Gstar t (sSAOrder s S A x) := by
    intro x
    by_cases h : x < s ∨ x ∈ A
    · have hx' : sSAOrder s S A x = S := by unfold sSAOrder; rw [if_pos h]
      rw [hx']
      have hlt : M.Gstar t x < M.Gstar t S - M.k := by
        rcases h with h | h
        · have := hs_left x h; linarith
        · exact h.2
      have hxS : x < S := by
        rcases h with h | h
        · exact lt_of_lt_of_le h hsS
        · have hxm : x ≤ (s + S) / 2 := h.1.2
          rcases lt_or_eq_of_le (show x ≤ S by linarith) with h' | h'
          · exact h'
          · exfalso; rw [h'] at hlt; linarith
      refine ⟨hxS.le, fun y hy => ?_⟩
      rw [hδ1 x S hxS]
      rcases eq_or_lt_of_le hy with h' | h'
      · rw [← h', hδ0]; linarith
      · rw [hδ1 x y h']; linarith [hSmax y]
    · have hx' : sSAOrder s S A x = x := by unfold sSAOrder; rw [if_neg h]
      rw [hx']
      push_neg at h
      obtain ⟨hsx, hxA⟩ := h
      refine ⟨le_rfl, fun y hy => ?_⟩
      rcases eq_or_lt_of_le hy with h' | h'
      · rw [← h', hδ0]
      · rw [hδ0, hδ1 x y h']
        by_cases hm : (s + S) / 2 ≤ x
        · have := hright' x y hm hy
          linarith
        · push_neg at hm
          have hnot : ¬ (M.Gstar t x < M.Gstar t S - M.k) := fun hl => hxA ⟨⟨hsx, hm.le⟩, hl⟩
          push_neg at hnot
          linarith [hSmax y]
  refine ⟨s, S, A, dsel, hsS, ?_, fun y => ⟨hdsel1 y, isMaxOn_iff.2 (hdsel2 y)⟩, fun x => ?_⟩
  · intro x hx; exact hx.1
  · obtain ⟨h1, h2⟩ := hmain x
    refine ⟨h1, fun y hy => h2 y hy, ?_⟩
    have hGreat : IsGreatest ((fun y => -M.k * δ (y - x) + M.Gstar t y) '' Set.Ici x)
        (-M.k * δ (sSAOrder s S A x - x) + M.Gstar t (sSAOrder s S A x)) :=
      ⟨⟨_, Set.mem_Ici.2 h1, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact h2 y hy⟩
    rw [csl_vformula M t ht x]
    unfold orderEnvelope
    rw [hGreat.csSup_eq]
    rfl

theorem csl_thm_4_1 (M : Model) (hA : M.Assumptions) :
    ∀ t ∈ Finset.Icc 1 M.T,
      (SymKConvex M.k (fun y => -M.Gstar t y) ∧
       SymKConvex M.k (fun x => -M.v t x)) ∧
      ∃ (s S : ℝ) (A : Set ℝ) (dsel : ℝ → ℝ),
        s ≤ S ∧ A ⊆ Set.Icc s ((s + S) / 2) ∧
        (∀ y : ℝ, dsel y ∈ Set.Icc (M.dlo t) (M.dhi t) ∧
          IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) (dsel y)) ∧
        ∀ x : ℝ,
          x ≤ sSAOrder s S A x ∧
          (∀ y, x ≤ y →
            M.orderObj t x y ≤ M.orderObj t x (sSAOrder s S A x)) ∧
          M.v t x = M.c t * x + M.orderObj t x (sSAOrder s S A x) := by
  intro t ht
  obtain ⟨hP, hI⟩ := csl_period M hA t ht
  exact ⟨⟨hP.2.2.2.2.2.1, hI.2.1⟩, csl_policy M hA t ht hP⟩

end ChenSimchiLevi.General

open ChenSimchiLevi.General in
theorem solution (M : Model) (hA : M.Assumptions) :
    ∀ t ∈ Finset.Icc 1 M.T,
      (SymKConvex M.k (fun y => -M.Gstar t y) ∧
       SymKConvex M.k (fun x => -M.v t x)) ∧
      ∃ (s S : ℝ) (A : Set ℝ) (dsel : ℝ → ℝ),
        s ≤ S ∧ A ⊆ Set.Icc s ((s + S) / 2) ∧
        (∀ y : ℝ, dsel y ∈ Set.Icc (M.dlo t) (M.dhi t) ∧
          IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) (dsel y)) ∧
        ∀ x : ℝ,
          x ≤ sSAOrder s S A x ∧
          (∀ y, x ≤ y →
            M.orderObj t x y ≤ M.orderObj t x (sSAOrder s S A x)) ∧
          M.v t x = M.c t * x + M.orderObj t x (sSAOrder s S A x) := by
  exact csl_thm_4_1 M hA
