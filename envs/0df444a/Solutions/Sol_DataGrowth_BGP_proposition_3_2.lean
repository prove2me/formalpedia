-- Prove2me | solution 2 for DataGrowth.BGP.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:48:20.176387+00:00
-- url     : https://prove2.me/submissions/86727c10-3ef6-48c9-be80-73ddda753e85

import Mathlib
import Definitions.Def_DataGrowth_BGP_DecEconomy
import Definitions.Def_DataGrowth_BGP_Planner
import Theorems.Thm_DataGrowth_BGP_lemma_A_1

-- carved verbatim out of submission 2d5ee8fd-cddc-423d-9c4f-b7100c9f043e, lines 419-448

section
set_option autoImplicit false
open DataGrowth.BGP

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
    DataGrowth.BGP.lemma_A_1 E.lE E.lR R.glE R.glR hlE hlR (fun t ht => (heq t ht).2.1)
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

theorem bgp_plan_all (P : Params) (hP : P.Standing) (S : PlanPath) (Q : PlanRates)
    (hS : IsPlanBGP P S Q) :
    Q.glR = 0 ∧ Q.glE = 0 ∧ 0 < Q.gN ∧ (P.ζ - 1) * Q.gN + P.ξ * Q.gphi + P.n = 0 ∧
      Q.gc = Q.gN ∧ Q.gc = (1 / P.γ) * (Q.gN - P.σ * Q.gphi) := by
  obtain ⟨heq, hc, hphi, hN, hlR, hlE, hlam, hmu⟩ := hS
  obtain ⟨hn, hρ, hγ, hγ1, hσ, hβ, hβ1, hψ, hη, hξ, hξ1, hζ, hζ1, hL0⟩ := hP
  obtain ⟨hlE0, hlR0, -⟩ := DataGrowth.BGP.lemma_A_1 S.lE S.lR Q.glE Q.glR hlE hlR
    (fun t ht => (heq t ht).2.1)
  have h1β : 0 < 1 - P.β := sub_pos.mpr hβ1
  have hA : 0 < P.Aconst := by
    unfold Params.Aconst
    exact Real.rpow_pos_of_pos (div_pos hψ h1β) _
  have hσ0 : 0 < P.σ := by linarith
  have hγne : P.γ ≠ 0 := hγ.ne'
  obtain ⟨hgN, hfr⟩ := bgp_frontier P hη hL0 S.N S.phi S.lR Q.gN Q.gphi Q.glR hN hphi hlR
    (fun t ht => (heq t ht).2.2.1)
  rw [hlR0] at hfr
  have a13 : (P.ζ - 1) * Q.gN + P.ξ * Q.gphi + P.n = 0 := by linarith
  have LN := bgp_LG_of_growth hN
  have Lphi := bgp_LG_of_growth hphi
  have LlR := bgp_LG_of_growth hlR
  have LlE := bgp_LG_of_growth hlE
  have Llam := bgp_LG_of_growth hlam
  have Lmu := bgp_LG_of_growth hmu
  have Lc := bgp_LG_of_growth hc
  have Lpop := bgp_LG_pop P hL0
  -- (26)
  have hgc : Q.gc = Q.gN + Q.glE := by
    have hR : BgpLG (fun s => P.Aconst * P.β * S.N s * S.lE s) (Q.gN + Q.glE) :=
      bgp_LG_mul (bgp_LG_const_mul (mul_pos hA hβ) LN) LlE
    exact bgp_LG_unique Lc (bgp_LG_congr hR (fun t ht => ((heq t ht).2.2.2.1).symm))
  have hgcN : Q.gc = Q.gN := by rw [hgc, hlE0]; ring
  -- (A.7)
  have e7 : Q.glam = -P.γ * Q.gc := by
    have hR : BgpLG (fun s => S.c s ^ (-P.γ)) (-P.γ * Q.gc) := bgp_LG_rpow Lc _
    refine bgp_LG_unique Llam (bgp_LG_congr hR (fun t ht => ?_))
    have h := (heq t ht).2.2.2.2.1
    try dsimp only
    linarith
  -- (A.8)
  have e8 : (P.σ - 1) * Q.gphi = Q.gmu + P.ζ * Q.gN + (P.ξ - 1) * Q.gphi + (1 - P.ξ) * Q.glR + P.n := by
    have hL : BgpLG (fun s => P.σ * S.phi s ^ (P.σ - 1)) ((P.σ - 1) * Q.gphi) :=
      bgp_LG_const_mul hσ0 (bgp_LG_rpow Lphi _)
    have hR : BgpLG (fun s => P.ξ * P.η * S.mu s * S.N s ^ P.ζ * S.phi s ^ (P.ξ - 1) *
        S.lR s ^ (1 - P.ξ) * P.pop s)
        (Q.gmu + P.ζ * Q.gN + (P.ξ - 1) * Q.gphi + (1 - P.ξ) * Q.glR + P.n) :=
      bgp_LG_mul (bgp_LG_mul (bgp_LG_mul (bgp_LG_mul
        (bgp_LG_const_mul (mul_pos hξ hη) Lmu) (bgp_LG_rpow LN _)) (bgp_LG_rpow Lphi _))
        (bgp_LG_rpow LlR _)) Lpop
    refine bgp_LG_unique (bgp_LG_congr hL (fun t ht => ?_)) hR
    have h := (heq t ht).2.2.2.2.2.1
    try dsimp only
    linear_combination (-1) * h
  -- (A.9)
  have e9 : Q.glam + Q.gN = Q.gmu + P.ζ * Q.gN + P.ξ * Q.gphi + (-P.ξ) * Q.glR + P.n := by
    have hL : BgpLG (fun s => P.β * P.Aconst * S.lam s * S.N s) (Q.glam + Q.gN) :=
      bgp_LG_mul (bgp_LG_const_mul (mul_pos hβ hA) Llam) LN
    have hR : BgpLG (fun s => P.η * (1 - P.ξ) * S.mu s * S.N s ^ P.ζ * S.phi s ^ P.ξ *
        S.lR s ^ (-P.ξ) * P.pop s)
        (Q.gmu + P.ζ * Q.gN + P.ξ * Q.gphi + (-P.ξ) * Q.glR + P.n) :=
      bgp_LG_mul (bgp_LG_mul (bgp_LG_mul (bgp_LG_mul
        (bgp_LG_const_mul (mul_pos hη (sub_pos.mpr hξ1)) Lmu) (bgp_LG_rpow LN _))
        (bgp_LG_rpow Lphi _)) (bgp_LG_rpow LlR _)) Lpop
    refine bgp_LG_unique (bgp_LG_congr hL (fun t ht => ?_)) hR
    have h := (heq t ht).2.2.2.2.2.2.1
    try dsimp only
    linear_combination h
  rw [hlR0] at e8 e9
  have hglam : Q.glam = P.σ * Q.gphi - Q.gN := by linarith
  have hg : P.γ * Q.gc = Q.gN - P.σ * Q.gphi := by linarith
  refine ⟨hlR0, hlE0, hgN, a13, hgcN, ?_⟩
  field_simp
  linarith

theorem solution (P : Params) (hP : P.Standing) (hγ : 1 < P.γ)
    (E : DecPath) (R : DecRates) (hE : IsDecBGP P E R)
    (S : PlanPath) (Q : PlanRates) (hS : IsPlanBGP P S Q) :
    Q.gc = R.gc ∧ Q.gN = R.gN ∧ Q.gphi = R.gphi ∧ Q.glR = R.glR ∧ Q.glE = R.glE ∧
      HasConstGrowth (fun t => P.Aconst * S.N t * S.lE t) R.gc := by
  obtain ⟨hgNd, a3⟩ := bgp_dec_A3 P hP E R hE
  obtain ⟨hgcd, a5⟩ := bgp_dec_A5 P hP E R hE
  obtain ⟨hlRd, hlEd, -⟩ := bgp_dec_basic P E R hE
  obtain ⟨hlRp, hlEp, hgNp, a13, hgcp, hg⟩ := bgp_plan_all P hP S Q hS
  have hγ0 : P.γ ≠ 0 := by obtain ⟨-, -, h, -⟩ := hP; exact h.ne'
  obtain ⟨-, h1d, h2d⟩ := bgp_rates P hP R.gN R.gphi hgNd a3 (by linarith)
  obtain ⟨-, h1p, h2p⟩ := bgp_rates P hP Q.gN Q.gphi hgNp a13 (by
    rw [hgcp] at hg
    field_simp at hg
    linarith)
  have hgNeq : Q.gN = R.gN := by rw [h1p, h1d]
  have hgcR : R.gc = Q.gN := by rw [hgcd, hgNeq]
  obtain ⟨-, -, -, hN, -, hlE, -, -⟩ := hS
  refine ⟨by rw [hgcp, hgNeq, hgcd], hgNeq, by rw [h2p, h2d], by rw [hlRp, hlRd],
    by rw [hlEp, hlEd], ?_⟩
  have hA : 0 < P.Aconst := by
    obtain ⟨hn, hρ, hγ, hγ1, hσ, hβ, hβ1, hψ, hη, hξ, hξ1, hζ, hζ1, hL0⟩ := hP
    unfold Params.Aconst
    exact Real.rpow_pos_of_pos (div_pos hψ (sub_pos.mpr hβ1)) _
  intro t ht
  refine ⟨mul_pos (mul_pos hA (hN t ht).1) (hlE t ht).1, ?_⟩
  refine (((hN t ht).2.const_mul P.Aconst).mul (hlE t ht).2).congr_deriv ?_
  rw [hlEp, hgcR]
  ring

end
