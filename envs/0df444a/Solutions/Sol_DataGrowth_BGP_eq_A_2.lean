-- Prove2me | solution 1 for DataGrowth.BGP.eq_A_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:35:08.160855+00:00
-- url     : https://prove2.me/submissions/9b0d653c-7e59-4a54-8d24-b3cb7ab67094

import Mathlib
import Definitions.Def_DataGrowth_BGP_DecEconomy

set_option autoImplicit false
open DataGrowth.BGP

/-- log-derivative predicate: positive for t > 0 with constant logarithmic derivative. -/
def BgpLG (f : ℝ → ℝ) (g : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → 0 < f t ∧ HasDerivAt (fun s => Real.log (f s)) g t

theorem bgp_LG_of_growth {x : ℝ → ℝ} {g : ℝ} (h : HasConstGrowth x g) : BgpLG x g := by
  intro t ht
  obtain ⟨hp, hd⟩ := h t ht
  refine ⟨hp, ?_⟩
  have := hd.log hp.ne'
  rwa [mul_div_assoc, div_self hp.ne', mul_one] at this

theorem bgp_LG_congr {f f' : ℝ → ℝ} {g : ℝ} (h : BgpLG f g)
    (he : ∀ t : ℝ, 0 < t → f t = f' t) : BgpLG f' g := by
  intro t ht
  obtain ⟨hp, hd⟩ := h t ht
  refine ⟨he t ht ▸ hp, ?_⟩
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [he s hs]

theorem bgp_LG_unique {f : ℝ → ℝ} {a b : ℝ} (ha : BgpLG f a) (hb : BgpLG f b) : a = b :=
  ((ha 1 one_pos).2).unique ((hb 1 one_pos).2)

theorem bgp_LG_mul {f g : ℝ → ℝ} {a b : ℝ} (hf : BgpLG f a) (hg : BgpLG g b) :
    BgpLG (fun s => f s * g s) (a + b) := by
  intro t ht
  obtain ⟨hp, hd⟩ := hf t ht
  obtain ⟨hp', hd'⟩ := hg t ht
  refine ⟨mul_pos hp hp', ?_⟩
  refine (hd.add hd').congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact Real.log_mul (hf s hs).1.ne' (hg s hs).1.ne'

theorem bgp_LG_rpow {f : ℝ → ℝ} {a : ℝ} (hf : BgpLG f a) (p : ℝ) :
    BgpLG (fun s => f s ^ p) (p * a) := by
  intro t ht
  obtain ⟨hp, hd⟩ := hf t ht
  refine ⟨Real.rpow_pos_of_pos hp p, ?_⟩
  refine (hd.const_mul p).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact Real.log_rpow (hf s hs).1 p

theorem bgp_LG_const {c : ℝ} (hc : 0 < c) : BgpLG (fun _ => c) 0 := by
  intro t ht
  exact ⟨hc, hasDerivAt_const t (Real.log c)⟩

theorem bgp_LG_const_mul {f : ℝ → ℝ} {a c : ℝ} (hc : 0 < c) (hf : BgpLG f a) :
    BgpLG (fun s => c * f s) a := by
  have := bgp_LG_mul (bgp_LG_const hc) hf
  simpa using this

theorem bgp_LG_exp (n : ℝ) : BgpLG (fun s => Real.exp (n * s)) n := by
  intro t ht
  refine ⟨Real.exp_pos _, ?_⟩
  simp only [Real.log_exp]
  simpa using (hasDerivAt_id t).const_mul n

theorem bgp_LG_pop (P : Params) (hL0 : 0 < P.L0) : BgpLG P.pop P.n :=
  bgp_LG_congr (bgp_LG_const_mul hL0 (bgp_LG_exp P.n)) (fun t _ => rfl)

theorem bgp_const_growth_zero {x : ℝ → ℝ} {g c : ℝ} (hx : HasConstGrowth x g)
    (hc : ∀ t : ℝ, 0 < t → x t = c) : g = 0 := by
  have h1 := (hx 1 one_pos).2
  have h2 : HasDerivAt x 0 1 := by
    refine (hasDerivAt_const (1:ℝ) c).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (one_pos : (0:ℝ) < 1)] with s hs using hc s hs
  have := h1.unique h2
  have hp := (hx 1 one_pos).1
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hp.ne'

theorem bgp_const_of_zero {x : ℝ → ℝ} (hx : HasConstGrowth x 0) :
    ∀ t : ℝ, 0 < t → x t = x 1 := by
  have hd : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt x 0 t := by
    intro t ht
    have := (hx t ht).2
    simpa using this
  intro t ht
  exact (isOpen_Ioi (a := (0:ℝ))).is_const_of_deriv_eq_zero (isPreconnected_Ioi)
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht (Set.mem_Ioi.mpr one_pos)

theorem bgp_lemA1 (a b : ℝ → ℝ) (ga gb : ℝ) (ha : HasConstGrowth a ga)
    (hb : HasConstGrowth b gb) (hsum : ∀ t : ℝ, 0 < t → a t + b t = 1) :
    ga = 0 ∧ gb = 0 ∧ ∃ a0 b0 : ℝ, ∀ t : ℝ, 0 < t → a t = a0 ∧ b t = b0 := by
  have key : ∀ t : ℝ, 0 < t → ga * a t + gb * b t = 0 := by
    intro t ht
    have h1 : HasDerivAt (fun s => a s + b s) (ga * a t + gb * b t) t :=
      (ha t ht).2.add (hb t ht).2
    have h2 : HasDerivAt (fun s => a s + b s) 0 t := by
      refine (hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht] with s hs using hsum s hs
    exact h1.unique h2
  have hg : ga = gb := by
    by_contra hne
    have hne' : ga - gb ≠ 0 := sub_ne_zero.mpr hne
    have hc : ∀ t : ℝ, 0 < t → a t = -gb / (ga - gb) := by
      intro t ht
      have h : (ga - gb) * a t = -gb := by
        linear_combination key t ht - gb * hsum t ht
      rw [eq_div_iff hne']
      linarith
    have hga : ga = 0 := bgp_const_growth_zero ha hc
    have hgb : gb = 0 := bgp_const_growth_zero hb (c := 1 - (-gb / (ga - gb)))
      (fun t ht => by have := hsum t ht; rw [hc t ht] at this; linarith)
    exact hne (by rw [hga, hgb])
  have hga : ga = 0 := by
    have := key 1 one_pos
    have h1 := hsum 1 one_pos
    rw [← hg] at this
    have : ga * (a 1 + b 1) = 0 := by linarith
    rw [h1] at this
    linarith
  have hgb : gb = 0 := by rw [← hg]; exact hga
  refine ⟨hga, hgb, a 1, b 1, fun t ht => ⟨?_, ?_⟩⟩
  · subst hga; exact bgp_const_of_zero ha t ht
  · subst hgb; exact bgp_const_of_zero hb t ht

theorem bgp_frontier (P : Params) (hη : 0 < P.η) (hL0 : 0 < P.L0) (N φ lR : ℝ → ℝ)
    (gN gφ glR : ℝ) (hN : HasConstGrowth N gN) (hφ : HasConstGrowth φ gφ)
    (hlR : HasConstGrowth lR glR)
    (h : ∀ t : ℝ, 0 < t → HasDerivAt N
      (P.η * N t ^ P.ζ * φ t ^ P.ξ * lR t ^ (1 - P.ξ) * P.pop t) t) :
    0 < gN ∧ gN = P.ζ * gN + P.ξ * gφ + (1 - P.ξ) * glR + P.n := by
  have hEq : ∀ t : ℝ, 0 < t →
      gN * N t = P.η * N t ^ P.ζ * φ t ^ P.ξ * lR t ^ (1 - P.ξ) * P.pop t := by
    intro t ht
    exact ((hN t ht).2).unique (h t ht)
  have hpop : 0 < P.pop 1 := by unfold Params.pop; positivity
  have hrhs : 0 < P.η * N 1 ^ P.ζ * φ 1 ^ P.ξ * lR 1 ^ (1 - P.ξ) * P.pop 1 := by
    have h1 := (hN 1 one_pos).1
    have h2 := (hφ 1 one_pos).1
    have h3 := (hlR 1 one_pos).1
    positivity
  have hgN : 0 < gN := by
    by_contra hle
    push_neg at hle
    have h1 := hEq 1 one_pos
    have h2 := (hN 1 one_pos).1
    nlinarith
  have hL : BgpLG (fun s => gN * N s) gN := bgp_LG_const_mul hgN (bgp_LG_of_growth hN)
  have hR : BgpLG (fun s => P.η * N s ^ P.ζ * φ s ^ P.ξ * lR s ^ (1 - P.ξ) * P.pop s)
      (P.ζ * gN + P.ξ * gφ + (1 - P.ξ) * glR + P.n) :=
    bgp_LG_mul (bgp_LG_mul (bgp_LG_mul
      (bgp_LG_const_mul hη (bgp_LG_rpow (bgp_LG_of_growth hN) P.ζ))
      (bgp_LG_rpow (bgp_LG_of_growth hφ) P.ξ))
      (bgp_LG_rpow (bgp_LG_of_growth hlR) (1 - P.ξ))) (bgp_LG_pop P hL0)
  exact ⟨hgN, bgp_LG_unique (bgp_LG_congr hL hEq) hR⟩

theorem bgp_rates (P : Params) (hP : P.Standing) (gN gφ : ℝ) (hgN : 0 < gN)
    (a3 : (P.ζ - 1) * gN + P.ξ * gφ + P.n = 0)
    (hrel : P.σ * gφ = (1 - P.γ) * gN) :
    0 < P.denom ∧ gN = P.gStar ∧ gφ = P.gPhiStar := by
  obtain ⟨hn, hρ, hγ, hγ1, hσ, hβ, hβ1, hψ, hη, hξ, hξ1, hζ, hζ1, hL0⟩ := hP
  have hσ0 : 0 < P.σ := by linarith
  have hD : P.denom * gN = P.σ * P.n := by
    unfold Params.denom
    linear_combination (-P.σ) * a3 + P.ξ * hrel
  have hDpos : 0 < P.denom := by
    by_contra hle
    push_neg at hle
    have : 0 < P.σ * P.n := by positivity
    nlinarith
  refine ⟨hDpos, ?_, ?_⟩
  · unfold Params.gStar
    rw [eq_div_iff hDpos.ne']
    linarith
  · unfold Params.gPhiStar
    rw [eq_div_iff hDpos.ne']
    have h0 : P.σ * (gφ * P.denom - (1 - P.γ) * P.n) = 0 := by
      linear_combination P.denom * hrel + (1 - P.γ) * hD
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (by positivity)
    · linarith

theorem bgp_dec_basic (P : Params) (E : DecPath) (R : DecRates) (hE : IsDecBGP P E R) :
    R.glR = 0 ∧ R.glE = 0 ∧ ∃ lE0 lR0 : ℝ, ∀ t : ℝ, 0 < t → E.lE t = lE0 ∧ E.lR t = lR0 := by
  obtain ⟨heq, hr, hc, hphi, hN, hlR, hlE, hV, hw, hp, hy⟩ := hE
  obtain ⟨h1, h2, a0, b0, hab⟩ :=
    bgp_lemA1 E.lE E.lR R.glE R.glR hlE hlR (fun t ht => (heq t ht).2.1)
  exact ⟨h2, h1, a0, b0, hab⟩

theorem bgp_dec_A3 (P : Params) (hP : P.Standing) (E : DecPath) (R : DecRates)
    (hE : IsDecBGP P E R) :
    0 < R.gN ∧ (P.ζ - 1) * R.gN + P.ξ * R.gphi + P.n = 0 := by
  obtain ⟨hlR0, hlE0, -⟩ := bgp_dec_basic P E R hE
  obtain ⟨heq, hr, hc, hphi, hN, hlR, hlE, hV, hw, hp, hy⟩ := hE
  obtain ⟨hn, hρ, hγ, hγ1, hσ, hβ, hβ1, hψ, hη, hξ, hξ1, hζ, hζ1, hL0⟩ := hP
  obtain ⟨hpos, hrel⟩ := bgp_frontier P hη hL0 E.N E.phi E.lR R.gN R.gphi R.glR hN hphi hlR
    (fun t ht => (heq t ht).2.2.2.2.2.2.2.2.2.2.1)
  rw [hlR0] at hrel
  exact ⟨hpos, by linarith⟩

theorem bgp_dec_A2 (P : Params) (hP : P.Standing) (E : DecPath) (R : DecRates)
    (hE : IsDecBGP P E R) :
    P.n < R.rstar ∧ (∀ t : ℝ, 0 < t → E.V t = E.pi t / (R.rstar - P.n)) ∧ R.gV = P.n := by
  obtain ⟨-, -, ⟨lE0, lR0, hl⟩⟩ := bgp_dec_basic P E R hE
  obtain ⟨heq, hr, hc, hphi, hN, hlR, hlE, hV, hw, hp, hy⟩ := hE
  obtain ⟨hn, hρ, hγ, hγ1, hσ, hβ, hβ1, hψ, hη, hξ, hξ1, hζ, hζ1, hL0⟩ := hP
  have h1β : 0 < 1 - P.β := sub_pos.mpr hβ1
  have hKpi : 0 < P.Kpi := by
    unfold Params.Kpi
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hψ _) hβ) (Real.rpow_pos_of_pos h1β _)
  have hlE0 : 0 < lE0 := by
    have := (heq 1 one_pos).1.2.2.2.2.1
    rw [(hl 1 one_pos).1] at this
    exact this
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = P.Kpi * lE0 * P.L0 := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hC]; positivity
  have hpi : ∀ s : ℝ, 0 < s → E.pi s = C * Real.exp (P.n * s) := by
    intro s hs
    have h13 := (heq s hs).2.2.2.2.2.1
    rw [h13, (hl s hs).1, hC]
    unfold Params.pop
    ring
  have hmain : ∀ t : ℝ, 0 < t → P.n < R.rstar ∧ E.V t = E.pi t / (R.rstar - P.n) := by
    intro t ht
    have hint := (heq t ht).2.2.2.2.2.2.2.2.1
    have hVdef := (heq t ht).2.2.2.2.2.2.2.2.2.1
    have hI : ∀ s ∈ Set.Ioi t, ∫ τ in t..s, E.r τ = (s - t) * R.rstar := by
      intro s hs
      have hts : t ≤ s := le_of_lt hs
      have h0 : ∫ τ in t..s, E.r τ = ∫ τ in t..s, R.rstar := by
        apply intervalIntegral.integral_congr
        intro τ hτ
        rw [Set.uIcc_of_le hts] at hτ
        exact hr τ (lt_of_lt_of_le ht hτ.1)
      rw [h0, intervalIntegral.integral_const, smul_eq_mul]
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C * Real.exp (R.rstar * t) := ⟨_, rfl⟩
    have hKpos : 0 < K := by rw [hK]; positivity
    have hfun : Set.EqOn (fun s => Real.exp (-∫ τ in t..s, E.r τ) * E.pi s)
        (fun s => K * Real.exp ((P.n - R.rstar) * s)) (Set.Ioi t) := by
      intro s hs
      have hs0 : 0 < s := lt_trans ht hs
      try dsimp only
      rw [hI s hs, hpi s hs0, hK]
      have e : Real.exp (-((s - t) * R.rstar)) * Real.exp (P.n * s)
          = Real.exp (R.rstar * t) * Real.exp ((P.n - R.rstar) * s) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc Real.exp (-((s - t) * R.rstar)) * (C * Real.exp (P.n * s))
          = C * (Real.exp (-((s - t) * R.rstar)) * Real.exp (P.n * s)) := by ring
        _ = C * Real.exp (R.rstar * t) * Real.exp ((P.n - R.rstar) * s) := by rw [e]; ring
    have hint2 : MeasureTheory.IntegrableOn (fun s => K * Real.exp ((P.n - R.rstar) * s))
        (Set.Ioi t) := hint.congr_fun hfun measurableSet_Ioi
    have hlt : P.n - R.rstar < 0 := by
      by_contra hge
      push_neg at hge
      have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => K) (Set.Ioi t) := by
        refine MeasureTheory.Integrable.mono' hint2 MeasureTheory.aestronglyMeasurable_const ?_
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (MeasureTheory.ae_of_all _ fun s hs => ?_)
        have hs0 : 0 < s := lt_trans ht hs
        have h1 : 1 ≤ Real.exp ((P.n - R.rstar) * s) :=
          Real.one_le_exp (mul_nonneg hge hs0.le)
        rw [Real.norm_eq_abs, abs_of_pos hKpos]
        nlinarith
      rcases (MeasureTheory.integrableOn_const_iff).mp hconst with h | h
      · simp at h
        linarith
      · simp [Real.volume_Ioi] at h
    have hVt : E.V t = K * (-Real.exp ((P.n - R.rstar) * t) / (P.n - R.rstar)) := by
      rw [hVdef, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfun,
        MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hlt t]
    refine ⟨by linarith, ?_⟩
    rw [hVt, hpi t ht, hK]
    have e : Real.exp (R.rstar * t) * Real.exp ((P.n - R.rstar) * t) = Real.exp (P.n * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc C * Real.exp (R.rstar * t) * (-Real.exp ((P.n - R.rstar) * t) / (P.n - R.rstar))
        = -(C * (Real.exp (R.rstar * t) * Real.exp ((P.n - R.rstar) * t))) / (P.n - R.rstar) := by
          ring
      _ = -(C * Real.exp (P.n * t)) / (-(R.rstar - P.n)) := by
          rw [e, show P.n - R.rstar = -(R.rstar - P.n) by ring]
      _ = C * Real.exp (P.n * t) / (R.rstar - P.n) := by rw [neg_div_neg_eq]
  have h1 := hmain 1 one_pos
  refine ⟨h1.1, fun t ht => (hmain t ht).2, ?_⟩
  have hrn : 0 < R.rstar - P.n := by linarith [h1.1]
  have hLG : BgpLG (fun s => C / (R.rstar - P.n) * Real.exp (P.n * s)) P.n :=
    bgp_LG_const_mul (by positivity) (bgp_LG_exp P.n)
  have hLG2 : BgpLG E.V P.n := bgp_LG_congr hLG (fun t ht => by
    try dsimp only
    rw [(hmain t ht).2, hpi t ht]
    ring)
  exact bgp_LG_unique (bgp_LG_of_growth hV) hLG2

theorem bgp_dec_A5 (P : Params) (hP : P.Standing) (E : DecPath) (R : DecRates)
    (hE : IsDecBGP P E R) :
    R.gc = R.gN ∧ (P.ζ - P.γ) * R.gN + (P.ξ - P.σ) * R.gphi + P.n = 0 := by
  obtain ⟨hnr, -, hgV⟩ := bgp_dec_A2 P hP E R hE
  obtain ⟨hlR0, hlE0, -⟩ := bgp_dec_basic P E R hE
  obtain ⟨heq, hr, hc, hphi, hN, hlR, hlE, hV, hw, hp, hy⟩ := hE
  obtain ⟨hn, hρ, hγ, hγ1, hσ, hβ, hβ1, hψ, hη, hξ, hξ1, hζ, hζ1, hL0⟩ := hP
  have h1β : 0 < 1 - P.β := sub_pos.mpr hβ1
  have hKy : 0 < P.Ky := by
    unfold Params.Ky
    exact Real.rpow_pos_of_pos (div_pos (pow_pos h1β 2) hψ) _
  have hγne : P.γ ≠ 0 := hγ.ne'
  have mdc : ∀ a b : ℝ, b ≠ 0 → a * b / b = a := fun a b hb => by
    rw [mul_div_assoc, div_self hb, mul_one]
  -- Euler (4)
  have e1 : P.γ * R.gc = R.rstar - P.ρ := by
    have h4 := (heq 1 one_pos).2.2.1
    have hu := ((hc 1 one_pos).2).unique h4
    rw [hr 1 one_pos] at hu
    have h' := mul_right_cancel₀ (hc 1 one_pos).1.ne' hu
    rw [h']
    field_simp
  -- (5)
  have e2 : R.gp - (P.σ - 1) * R.gphi = R.rstar - P.ρ := by
    obtain ⟨-, -, e5⟩ := (heq 1 one_pos).2.2.2.1
    rw [((hp 1 one_pos).2).deriv, ((hphi 1 one_pos).2).deriv, hr 1 one_pos,
      mdc _ _ (hp 1 one_pos).1.ne', mdc _ _ (hphi 1 one_pos).1.ne'] at e5
    exact e5
  -- output
  have hy' : BgpLG (fun s => P.Ky * E.N s * E.lE s) (R.gN + R.glE) :=
    bgp_LG_mul (bgp_LG_const_mul hKy (bgp_LG_of_growth hN)) (bgp_LG_of_growth hlE)
  have hgc : R.gc = R.gN + R.glE :=
    bgp_LG_unique (bgp_LG_of_growth hy) (bgp_LG_congr hy' (fun t _ => rfl))
  have hgcN : R.gc = R.gN := by rw [hgc, hlE0]; ring
  -- (18)
  have hR : BgpLG (fun s => P.η * P.ξ * E.N s ^ P.ζ * E.phi s ^ (P.ξ - 1) * E.lR s ^ (1 - P.ξ) * E.V s)
      (P.ζ * R.gN + (P.ξ - 1) * R.gphi + (1 - P.ξ) * R.glR + R.gV) :=
    bgp_LG_mul (bgp_LG_mul (bgp_LG_mul
      (bgp_LG_const_mul (mul_pos hη hξ) (bgp_LG_rpow (bgp_LG_of_growth hN) P.ζ))
      (bgp_LG_rpow (bgp_LG_of_growth hphi) (P.ξ - 1)))
      (bgp_LG_rpow (bgp_LG_of_growth hlR) (1 - P.ξ))) (bgp_LG_of_growth hV)
  have e3 : R.gp = P.ζ * R.gN + (P.ξ - 1) * R.gphi + (1 - P.ξ) * R.glR + R.gV :=
    bgp_LG_unique (bgp_LG_of_growth hp)
      (bgp_LG_congr hR (fun t ht => (heq t ht).2.2.2.2.2.2.2.2.2.2.2.1))
  rw [hlR0, hgV] at e3
  rw [hgcN] at e1
  refine ⟨hgcN, ?_⟩
  linarith

theorem solution (P : Params) (hP : P.Standing) (E : DecPath) (R : DecRates)
    (hE : IsDecBGP P E R) :
    (∀ t : ℝ, 0 < t → E.V t = E.pi t / (R.rstar - P.n)) ∧ R.gV = P.n :=
  ⟨(bgp_dec_A2 P hP E R hE).2.1, (bgp_dec_A2 P hP E R hE).2.2⟩
