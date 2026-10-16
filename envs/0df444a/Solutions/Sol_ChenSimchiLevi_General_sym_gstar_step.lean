-- Prove2me | solution 1 for ChenSimchiLevi.General.sym_gstar_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T04:39:20.139036+00:00
-- url     : https://prove2.me/submissions/4c4edb5d-5408-40cc-9933-4f930f711813

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

end ChenSimchiLevi.General

open ChenSimchiLevi.General in
theorem solution (M : Model) (hA : M.Assumptions)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (V : ℝ → ℝ)
    (hVcont : Continuous V) (hVsym : SymKConvex M.k (fun x => -V x))
    (hVgrowth : ∃ C : ℝ, ∀ x, |V x| ≤ C * (1 + |x| ^ M.ρ))
    (hgcont : ContinuousOn (fun q : ℝ × ℝ => M.gWith V t q.1 q.2)
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t))) :
    SymKConvex M.k (fun y => -M.GstarWith V t y) := by
  exact csl_sym_gstar_step M hA t ht V hVcont hVsym hVgrowth hgcont
