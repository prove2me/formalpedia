-- Prove2me | solution 1 for DataGrowth.BGP.eq_A_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:35:13.226988+00:00
-- url     : https://prove2.me/submissions/27072704-6518-4f67-b14f-6ac048b1debf

import Mathlib
import Definitions.Def_DataGrowth_BGP_Planner

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

theorem bgp_plan_all (P : Params) (hP : P.Standing) (S : PlanPath) (Q : PlanRates)
    (hS : IsPlanBGP P S Q) :
    Q.glR = 0 ∧ Q.glE = 0 ∧ 0 < Q.gN ∧ (P.ζ - 1) * Q.gN + P.ξ * Q.gphi + P.n = 0 ∧
      Q.gc = Q.gN ∧ Q.gc = (1 / P.γ) * (Q.gN - P.σ * Q.gphi) := by
  obtain ⟨heq, hc, hphi, hN, hlR, hlE, hlam, hmu⟩ := hS
  obtain ⟨hn, hρ, hγ, hγ1, hσ, hβ, hβ1, hψ, hη, hξ, hξ1, hζ, hζ1, hL0⟩ := hP
  obtain ⟨hlE0, hlR0, -⟩ := bgp_lemA1 S.lE S.lR Q.glE Q.glR hlE hlR
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

theorem solution (P : Params) (hP : P.Standing) (S : PlanPath) (Q : PlanRates)
    (hS : IsPlanBGP P S Q) :
    (P.ζ - 1) * Q.gN + P.ξ * Q.gphi + P.n = 0 :=
  (bgp_plan_all P hP S Q hS).2.2.2.1
