-- Prove2me | solution 1 for GenNewtonSubgrad.ProxReg.theorem_6_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:23:15.160424+00:00
-- url     : https://prove2.me/submissions/3a901336-3e12-424c-947d-b5f55c5986c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg62
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_i
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_iii
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_4
import Theorems.Thm_GenNewtonSubgrad_ProxReg_remark_6_5
import Theorems.Thm_GenNewtonSubgrad_Composite_theorem_5_7_local

open Filter Topology
open scoped InnerProductSpace

namespace GNC73
open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regN_gen (Φ : E × E → E × E) (Λ : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') {z a : E × E} (hz : z ∈ S) (ha : a ∈ regNormal S' (Φ z)) :
    adjm a ∈ regNormal S z := by
  refine ⟨hz, fun ε hε => ?_⟩
  have hΦc : Continuous Φ := by
    have : Φ = fun w => Φ 0 + Λ w := by
      funext w; have := hΦ w 0; rw [sub_zero] at this; rw [← this]; abel
    rw [this]; exact continuous_const.add Λ.continuous
  have hK : 0 < ‖Λ‖ + 1 := by positivity
  have h1 := ha.2 (ε / (‖Λ‖ + 1)) (div_pos hε hK)
  have h2 := (hΦc.tendsto z).eventually h1
  filter_upwards [h2] with w hw hwS
  have := hw (hS w hwS)
  rw [hadj, ← hΦ]
  refine this.trans ?_
  rw [hΦ]
  calc ε / (‖Λ‖ + 1) * ‖Λ (w - z)‖ ≤ ε / (‖Λ‖ + 1) * ((‖Λ‖ + 1) * ‖w - z‖) := by
        gcongr
        calc ‖Λ (w - z)‖ ≤ ‖Λ‖ * ‖w - z‖ := Λ.le_opNorm _
          _ ≤ (‖Λ‖ + 1) * ‖w - z‖ := by nlinarith [norm_nonneg (w - z)]
    _ = ε * ‖w - z‖ := by field_simp

lemma limN_gen (Φ Ψ : E × E → E × E) (Λ : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) (hadjc : Continuous adjm)
    (hΨc : Continuous Ψ) (hΦΨ : ∀ w, Φ (Ψ w) = w) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') (hS' : ∀ w ∈ S', Ψ w ∈ S) {z a : E × E} (hz : z ∈ S)
    (hΨΦ : Ψ (Φ z) = z) (ha : a ∈ limNormal S' (Φ z)) : adjm a ∈ limNormal S z := by
  obtain ⟨-, zs, as, hzs, hzl, hal, hreg⟩ := ha
  refine ⟨hz, fun k => Ψ (zs k), fun k => adjm (as k), fun k => hS' _ (hzs k), ?_,
    (hadjc.tendsto a).comp hal, fun k => ?_⟩
  · have := (hΨc.tendsto _).comp hzl
    rwa [hΨΦ] at this
  · apply regN_gen Φ Λ hΦ adjm hadj hS (hS' _ (hzs k))
    rw [hΦΨ]; exact hreg k

lemma regNormal_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N) {z : E × E}
    (hzN : z ∈ N) (a : E × E) : a ∈ regNormal S z → a ∈ regNormal S' z := by
  rintro ⟨hz, h⟩
  have hz' : z ∈ S' := by
    have : z ∈ S ∩ N := ⟨hz, hzN⟩
    rw [hSS] at this; exact this.1
  refine ⟨hz', fun ε hε => ?_⟩
  filter_upwards [h ε hε, hN.mem_nhds hzN] with w hw hwN hwS'
  have : w ∈ S' ∩ N := ⟨hwS', hwN⟩
  rw [← hSS] at this
  exact hw this.1

lemma limNormal_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N) {z : E × E}
    (hzN : z ∈ N) (a : E × E) : a ∈ limNormal S z → a ∈ limNormal S' z := by
  rintro ⟨hz, zs, as, hzs, hzl, hal, hreg⟩
  have hz' : z ∈ S' := by
    have : z ∈ S ∩ N := ⟨hz, hzN⟩
    rw [hSS] at this; exact this.1
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hzl.eventually (hN.mem_nhds hzN))
  have hsh : Tendsto (fun t : ℕ => t + K) atTop atTop := tendsto_add_atTop_nat K
  refine ⟨hz', fun k => zs (k + K), fun k => as (k + K), fun k => ?_, hzl.comp hsh, hal.comp hsh,
    fun k => regNormal_local hN hSS (hK _ (Nat.le_add_left K k)) _ (hreg _)⟩
  have : zs (k + K) ∈ S ∩ N := ⟨hzs _, hK _ (Nat.le_add_left K k)⟩
  rw [hSS] at this; exact this.1

lemma coderiv_congr (F G : E → E) {U : Set E} (hU : IsOpen U) (hFG : ∀ y ∈ U, F y = G y)
    {x : E} (hx : x ∈ U) (w : E) :
    coderiv (sv F) x (F x) w = coderiv (sv G) x (G x) w := by
  have hN : IsOpen (U ×ˢ (Set.univ : Set E)) := hU.prod isOpen_univ
  have hSS : gph (sv F) ∩ U ×ˢ Set.univ = gph (sv G) ∩ U ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      show p.2 ∈ ({G p.1} : Set E)
      have : p.2 ∈ ({F p.1} : Set E) := h1
      rwa [hFG p.1 h2] at this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      show p.2 ∈ ({F p.1} : Set E)
      have : p.2 ∈ ({G p.1} : Set E) := h1
      rwa [← hFG p.1 h2] at this
  have hzN : ((x, F x) : E × E) ∈ U ×ˢ (Set.univ : Set E) := ⟨hx, Set.mem_univ _⟩
  ext u
  show (u, -w) ∈ limNormal (gph (sv F)) (x, F x) ↔ (u, -w) ∈ limNormal (gph (sv G)) (x, G x)
  rw [← hFG x hx]
  exact ⟨limNormal_local hN hSS hzN _, limNormal_local hN hSS.symm hzN _⟩

end GNC73

namespace GNC75
open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNC73

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- the graph form of semismoothness* -/
def SSet (S : Set (E × E)) (z : E × E) : Prop :=
  ∀ d a : E × E, a ∈ dirLimNormal S z d → pairInner a d = 0

lemma semismooth_iff_SSet (G : E → Set E) (x y : E) :
    IsSemismoothStar G x y ↔ y ∈ G x ∧ SSet (gph G) (x, y) := by
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun d a ha => ?_⟩
    have h1 := h d.1 d.2 (-a.2) a.1 (by
      show (a.1, -(-a.2)) ∈ dirLimNormal (gph G) (x, y) (d.1, d.2)
      simpa using ha)
    simp only [pairInner]
    rw [inner_neg_left] at h1
    linarith
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun u v w u' hu' => ?_⟩
    have := h (u, v) (u', -w) hu'
    simp only [pairInner, inner_neg_left] at this
    linarith

lemma dirLimN_gen (Φ Ψ : E × E → E × E) (Λ Λi : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (hΛΛi : ∀ w, Λ (Λi w) = w)
    (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) (hadjc : Continuous adjm)
    (hΨΦ : ∀ w, Ψ (Φ w) = w) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') (hS' : ∀ w ∈ S', Ψ w ∈ S) {z a d : E × E} (hz : z ∈ S)
    (ha : a ∈ dirLimNormal S' (Φ z) (Λ d)) : adjm a ∈ dirLimNormal S z d := by
  obtain ⟨-, ts, ds, as, hts, htl, hdl, hal, hreg⟩ := ha
  refine ⟨hz, ts, fun k => Λi (ds k), fun k => adjm (as k), hts, htl, ?_,
    (hadjc.tendsto a).comp hal, fun k => ?_⟩
  · have hΛd : Λi (Λ d) = d := by
      have h1 : Λ (Λi (Λ d)) = Λ d := hΛΛi _
      -- Λ injective from Φ/Ψ
      have hinj : Function.Injective Λ := by
        intro p q hpq
        have e1 : Φ p - Φ 0 = Φ q - Φ 0 := by rw [hΦ, hΦ, sub_zero, sub_zero, hpq]
        have e2 : Φ p = Φ q := by simpa using e1
        have := congrArg Ψ e2
        rwa [hΨΦ, hΨΦ] at this
      exact hinj h1
    have := ((Λi.continuous).tendsto _).comp hdl
    rwa [hΛd] at this
  · have hk := hreg k
    have e : Φ z + ts k • ds k = Φ (z + ts k • Λi (ds k)) := by
      have := hΦ (z + ts k • Λi (ds k)) z
      rw [add_sub_cancel_left, map_smul, hΛΛi] at this
      rw [← this]; abel
    rw [e] at hk
    have hmem : z + ts k • Λi (ds k) ∈ S := by
      have := hS' _ hk.1
      rwa [hΨΦ] at this
    exact regN_gen Φ Λ hΦ adjm hadj hS hmem hk

lemma SSet_transfer (Φ Ψ : E × E → E × E) (Λ Λi : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (hΛΛi : ∀ w, Λ (Λi w) = w)
    (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) (hadjc : Continuous adjm)
    (hΨΦ : ∀ w, Ψ (Φ w) = w) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') (hS' : ∀ w ∈ S', Ψ w ∈ S) {z : E × E} (hz : z ∈ S)
    (h : SSet S z) : SSet S' (Φ z) := by
  intro d' a ha
  have ha' : a ∈ dirLimNormal S' (Φ z) (Λ (Λi d')) := by rw [hΛΛi]; exact ha
  have := h _ _ (dirLimN_gen Φ Ψ Λ Λi hΦ hΛΛi adjm hadj hadjc hΨΦ hS hS' hz ha')
  rw [hadj, hΛΛi] at this
  exact this

lemma dirLimNormal_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N)
    {z : E × E} (hzN : z ∈ N) (d a : E × E) :
    a ∈ dirLimNormal S z d → a ∈ dirLimNormal S' z d := by
  rintro ⟨hz, ts, ds, as, hts, htl, hdl, hal, hreg⟩
  have hz' : z ∈ S' := by
    have : z ∈ S ∩ N := ⟨hz, hzN⟩
    rw [hSS] at this; exact this.1
  have hpts : Tendsto (fun k => z + ts k • ds k) atTop (𝓝 z) := by
    have := tendsto_const_nhds (x := z) |>.add (htl.smul hdl)
    simpa using this
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hpts.eventually (hN.mem_nhds hzN))
  have hsh : Tendsto (fun t : ℕ => t + K) atTop atTop := tendsto_add_atTop_nat K
  exact ⟨hz', fun k => ts (k + K), fun k => ds (k + K), fun k => as (k + K), fun k => hts _,
    htl.comp hsh, hdl.comp hsh, hal.comp hsh,
    fun k => regNormal_local hN hSS (hK _ (Nat.le_add_left K k)) _ (hreg _)⟩

lemma SSet_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N)
    {z : E × E} (hzN : z ∈ N) (h : SSet S z) : SSet S' z := fun d a ha =>
  h d a (dirLimNormal_local hN hSS.symm hzN d a ha)

end GNC75

namespace GNC74
open GenNewtonSubgrad.ProxReg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma MR_transfer (G1 G2 : E → Set E) (xbar : E) (c : E →L[ℝ] E) {N : Set (E × E)}
    (hN : N ∈ 𝓝 ((xbar, 0) : E × E))
    (hloc : ∀ q ∈ N, q ∈ gph G2 ↔ ((q.1 - c q.2, q.2) : E × E) ∈ gph G1)
    (h : MetricRegularAround G1 xbar 0) : MetricRegularAround G2 xbar 0 := by
  obtain ⟨μ, h0, hμ, U1, hU1, V1, hV1, hreg⟩ := h
  obtain ⟨δN, hδN, hballN⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨δU, hδU, hballU⟩ := Metric.mem_nhds_iff.1 hU1
  obtain ⟨δV, hδV, hballV⟩ := Metric.mem_nhds_iff.1 hV1
  set δ := min δN (min δU δV) with hδdef
  have hδ : 0 < δ := lt_min hδN (lt_min hδU hδV)
  have hinN : ∀ x v : E, ‖x - xbar‖ < δ → ‖v‖ < δ → ((x, v) : E × E) ∈ N := by
    intro x v hx hv
    apply hballN
    rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm, sub_zero]
    exact max_lt (lt_of_lt_of_le hx (min_le_left _ _)) (lt_of_lt_of_le hv (min_le_left _ _))
  have hinU : ∀ x : E, ‖x - xbar‖ < δ → x ∈ U1 := by
    intro x hx; apply hballU
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have hinV : ∀ v : E, ‖v‖ < δ → v ∈ V1 := by
    intro v hv; apply hballV
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_lt_of_le hv ((min_le_right _ _).trans (min_le_right _ _))
  set κ := ‖c‖ with hκ
  have hκ0 : 0 ≤ κ := norm_nonneg _
  set M := 2 * μ + κ + 1 with hM
  have hM1 : 1 ≤ M := by linarith
  set δ' := δ / (2 * M + 2) with hδ'
  have hδ'pos : 0 < δ' := div_pos hδ (by linarith)
  set ρ := δ' / (2 * (M + 2)) with hρ
  have hρpos : 0 < ρ := div_pos hδ'pos (by linarith)
  have hδ'δ : (2 * M + 2) * δ' = δ := by rw [hδ']; field_simp
  have hMρ : (M + 2) * ρ * 2 = δ' := by rw [hρ]; field_simp
  have hρδ' : ρ ≤ δ' / 2 := by nlinarith
  have hρδ : ρ < δ := by nlinarith
  have hδ'lt : δ' < δ := by nlinarith
  have hcb : ∀ v : E, ‖c v‖ ≤ κ * ‖v‖ := fun v => c.le_opNorm v
  -- membership of xbar
  have h0' : (0 : E) ∈ G2 xbar := by
    have hq := hloc (xbar, 0) (hinN xbar 0 (by simpa using hδ) (by simpa using hδ))
    have : ((xbar - c 0, 0) : E × E) ∈ gph G1 := by
      show (0 : E) ∈ G1 (xbar - c 0); simpa using h0
    exact hq.2 this
  -- points of G2⁻¹ y from points of G1⁻¹ y
  have hlift : ∀ y p' : E, y ∈ G1 p' → ‖p' + c y - xbar‖ < δ → ‖y‖ < δ → y ∈ G2 (p' + c y) := by
    intro y p' hp' h1 h2
    have hq := hloc (p' + c y, y) (hinN _ _ h1 h2)
    exact hq.2 (by show y ∈ G1 (p' + c y - c y); simpa using hp')
  have hnear : ∀ y : E, ‖y‖ < ρ → ∃ x'' : E, y ∈ G2 x'' ∧ ‖x'' - xbar‖ < (μ + κ) * ρ := by
    intro y hy
    obtain ⟨hne, hd⟩ := hreg xbar (mem_of_mem_nhds hU1) y (hinV y (by linarith)) 0 h0
    have hlt : Metric.infDist xbar {x' | y ∈ G1 x'} < μ * ρ := by
      calc _ ≤ μ * ‖y - 0‖ := hd
        _ < μ * ρ := by rw [sub_zero]; exact mul_lt_mul_of_pos_left hy hμ
    obtain ⟨p', hp', hdp⟩ := (Metric.infDist_lt_iff hne).1 hlt
    rw [dist_comm, dist_eq_norm] at hdp
    have hx'' : ‖p' + c y - xbar‖ < (μ + κ) * ρ := by
      calc ‖p' + c y - xbar‖ ≤ ‖p' - xbar‖ + ‖c y‖ := by
            rw [show p' + c y - xbar = (p' - xbar) + c y by abel]; exact norm_add_le _ _
        _ < μ * ρ + κ * ρ := by
            have := hcb y
            have : κ * ‖y‖ ≤ κ * ρ := mul_le_mul_of_nonneg_left hy.le hκ0
            linarith
        _ = (μ + κ) * ρ := by ring
    refine ⟨p' + c y, hlift y p' hp' ?_ (by linarith), hx''⟩
    have : (μ + κ) * ρ ≤ δ := by nlinarith
    linarith
  refine ⟨M, h0', by linarith, Metric.ball xbar ρ, Metric.ball_mem_nhds _ hρpos,
    Metric.ball 0 ρ, Metric.ball_mem_nhds _ hρpos, fun x hx y hy w hw => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
  obtain ⟨x'', hx''G, hx''n⟩ := hnear y hy
  refine ⟨⟨x'', hx''G⟩, ?_⟩
  by_cases hwδ : ‖w‖ < δ'
  · -- case A
    have hpG : w ∈ G1 (x - c w) := by
      have hq := hloc (x, w) (hinN x w (by linarith) (by linarith))
      exact hq.1 hw
    have hpU : x - c w ∈ U1 := hinU _ (by
      calc ‖x - c w - xbar‖ ≤ ‖x - xbar‖ + ‖c w‖ := by
            rw [show x - c w - xbar = (x - xbar) - c w by abel]; exact norm_sub_le _ _
        _ < δ := by
            have := hcb w
            have : κ * ‖w‖ ≤ κ * δ' := mul_le_mul_of_nonneg_left hwδ.le hκ0
            nlinarith)
    obtain ⟨hne1, hd1⟩ := hreg (x - c w) hpU y (hinV y (by linarith)) w hpG
    by_cases hyw : y = w
    · subst hyw
      have : Metric.infDist x {x' | y ∈ G2 x'} ≤ 0 := by
        have := Metric.infDist_le_dist_of_mem (x := x) (show x ∈ {x' | y ∈ G2 x'} from hw)
        simpa using this
      have : 0 ≤ M * ‖y - y‖ := by simp
      linarith
    · have hpos : 0 < ‖y - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hyw)
      have hlt : Metric.infDist (x - c w) {x' | y ∈ G1 x'} < 2 * μ * ‖y - w‖ := by
        nlinarith
      obtain ⟨p', hp', hdp⟩ := (Metric.infDist_lt_iff hne1).1 hlt
      rw [dist_eq_norm] at hdp
      have hyw' : ‖y - w‖ < ρ + δ' := by
        calc ‖y - w‖ ≤ ‖y‖ + ‖w‖ := norm_sub_le _ _
          _ < ρ + δ' := by linarith
      have hx'n : ‖p' + c y - xbar‖ < δ := by
        have e : p' + c y - xbar = -((x - c w) - p') + (x - xbar) - c w + c y := by abel
        calc ‖p' + c y - xbar‖ ≤ ‖(x - c w) - p'‖ + ‖x - xbar‖ + ‖c w‖ + ‖c y‖ := by
              rw [e]
              calc ‖-((x - c w) - p') + (x - xbar) - c w + c y‖
                  ≤ ‖-((x - c w) - p') + (x - xbar) - c w‖ + ‖c y‖ := norm_add_le _ _
                _ ≤ ‖-((x - c w) - p') + (x - xbar)‖ + ‖c w‖ + ‖c y‖ := by
                    gcongr; exact norm_sub_le _ _
                _ ≤ ‖(x - c w) - p'‖ + ‖x - xbar‖ + ‖c w‖ + ‖c y‖ := by
                    gcongr; calc ‖-((x - c w) - p') + (x - xbar)‖
                        ≤ ‖-((x - c w) - p')‖ + ‖x - xbar‖ := norm_add_le _ _
                      _ = _ := by rw [norm_neg]
          _ < δ := by
              have h1 := hcb w
              have h2 := hcb y
              have h3 : κ * ‖w‖ ≤ κ * δ' := mul_le_mul_of_nonneg_left hwδ.le hκ0
              have h4 : κ * ‖y‖ ≤ κ * ρ := mul_le_mul_of_nonneg_left hy.le hκ0
              have h5 : 2 * μ * ‖y - w‖ ≤ 2 * μ * (ρ + δ') :=
                mul_le_mul_of_nonneg_left hyw'.le (by linarith)
              nlinarith
      have hx'G : y ∈ G2 (p' + c y) := hlift y p' hp' hx'n (by linarith)
      calc Metric.infDist x {x' | y ∈ G2 x'} ≤ dist x (p' + c y) :=
            Metric.infDist_le_dist_of_mem hx'G
        _ = ‖((x - c w) - p') + c (w - y)‖ := by
            rw [dist_eq_norm, map_sub]; congr 1; abel
        _ ≤ ‖(x - c w) - p'‖ + ‖c (w - y)‖ := norm_add_le _ _
        _ ≤ 2 * μ * ‖y - w‖ + κ * ‖y - w‖ := by
            have := hcb (w - y)
            rw [norm_sub_rev w y] at this
            linarith
        _ ≤ M * ‖y - w‖ := by nlinarith
  · -- case B
    push_neg at hwδ
    have hyw : δ' / 2 ≤ ‖y - w‖ := by
      have : ‖w‖ - ‖y‖ ≤ ‖y - w‖ := by
        rw [norm_sub_rev]; exact norm_sub_norm_le w y
      linarith
    calc Metric.infDist x {x' | y ∈ G2 x'} ≤ dist x x'' := Metric.infDist_le_dist_of_mem hx''G
      _ ≤ ‖x - xbar‖ + ‖x'' - xbar‖ := by
          rw [dist_eq_norm, show x - x'' = (x - xbar) - (x'' - xbar) by abel]; exact norm_sub_le _ _
      _ ≤ δ' / 2 := by nlinarith
      _ ≤ ‖y - w‖ := hyw
      _ ≤ M * ‖y - w‖ := by nlinarith [norm_nonneg (y - w)]

end GNC74

namespace GN66Aux
open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNC73 GNC75

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- the shear `(p, v) ↦ (p + λ v, v)` as a continuous linear map -/
noncomputable def shear (lam : ℝ) : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.fst ℝ E E + lam • ContinuousLinearMap.snd ℝ E E).prod
    (ContinuousLinearMap.snd ℝ E E)

@[simp] lemma shear_apply (lam : ℝ) (w : E × E) : shear lam w = (w.1 + lam • w.2, w.2) := by
  simp [shear]

lemma shear_inv (lam : ℝ) (w : E × E) : shear (-lam) (shear lam w) = w := by
  rcases w with ⟨a, b⟩
  simp [neg_smul]

lemma shear_inv' (lam : ℝ) (w : E × E) : shear lam (shear (-lam) w) = w := by
  rcases w with ⟨a, b⟩
  simp [neg_smul]

/-- Semismoothness* transfers along a local shear of graphs. -/
lemma semismooth_shear (G1 G2 : E → Set E) (xbar : E) (lam : ℝ) {N : Set (E × E)}
    (hNo : IsOpen N) (hzN : ((xbar, 0) : E × E) ∈ N)
    (hloc : ∀ q ∈ N, q ∈ gph G2 ↔ ((q.1 - lam • q.2, q.2) : E × E) ∈ gph G1)
    (h0 : (0 : E) ∈ G2 xbar)
    (h : IsSemismoothStar G1 xbar 0) : IsSemismoothStar G2 xbar 0 := by
  rw [semismooth_iff_SSet] at h ⊢
  refine ⟨h0, ?_⟩
  set Φ : E × E → E × E := fun w => shear lam w with hΦ
  set Ψ : E × E → E × E := fun w => shear (-lam) w with hΨ
  have hΦc : Continuous Φ := (shear lam).continuous
  have hlocΨ : ∀ q ∈ N, q ∈ gph G2 ↔ Ψ q ∈ gph G1 := by
    intro q hq
    rw [hloc q hq]
    simp [hΨ, neg_smul, sub_eq_add_neg]
  set S : Set (E × E) := gph G1 ∩ Φ ⁻¹' N with hS
  set S' : Set (E × E) := gph G2 ∩ N with hS'
  have hz : Φ ((xbar, 0) : E × E) = (xbar, 0) := by simp [hΦ]
  have h1 : SSet S ((xbar, 0) : E × E) := by
    refine SSet_local (hNo.preimage hΦc) (S := gph G1) ?_ (by show Φ _ ∈ N; rw [hz]; exact hzN)
      h.2
    ext w; simp only [hS, Set.mem_inter_iff, Set.mem_preimage]; tauto
  have h2 : SSet S' (Φ ((xbar, 0) : E × E)) := by
    refine SSet_transfer Φ Ψ (shear lam) (shear (-lam)) (fun w z => by simp [hΦ, map_sub])
      (shear_inv' lam) (fun a => (a.1, lam • a.1 + a.2)) ?_ ?_ (fun w => shear_inv lam w)
      ?_ ?_ ?_ h1
    · intro a h
      simp only [pairInner, shear_apply, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right]
      ring
    · exact continuous_fst.prodMk ((continuous_fst.const_smul lam).add continuous_snd)
    · rintro w ⟨hw1, hw2⟩
      refine ⟨(hlocΨ _ hw2).2 ?_, hw2⟩
      show shear (-lam) (shear lam w) ∈ gph G1
      rw [shear_inv]; exact hw1
    · rintro q ⟨hq1, hq2⟩
      refine ⟨(hlocΨ q hq2).1 hq1, ?_⟩
      show shear lam (shear (-lam) q) ∈ N
      rw [shear_inv']; exact hq2
    · exact ⟨h.1, by show Φ _ ∈ N; rw [hz]; exact hzN⟩
  rw [hz] at h2
  refine SSet_local hNo (S := S') ?_ hzN h2
  ext w; simp only [hS', Set.mem_inter_iff]; tauto

end GN66Aux

open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNC73 GNC75 GNC74 GN66Aux in
theorem solution {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar 0 r ε)
    (hH : StandingH (NonconvexSplitting.Shared.LimitingSubdiff φ) xbar 0) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ U ∈ 𝓝 xbar, U ⊆ rgeShift φ lam ∧ Alg62WellDefinedOn φ lam U ∧
        ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsAlg62Run φ lam x → x 0 ∈ U →
          IsQSuperlinear x xbar := by
  obtain ⟨l1, hl1, hl1r, HH1⟩ := lemma_6_3_i φ xbar 0 r ε hproper hbdd hreg
  obtain ⟨l3, hl3, -, H3⟩ := lemma_6_3_iii φ xbar 0 r ε hproper hbdd hreg
  obtain ⟨l4, hl4, -, H4⟩ := lemma_6_4 φ xbar 0 r ε hproper hbdd hreg
  obtain ⟨l5, hl5, -, H5⟩ := remark_6_5 φ xbar 0 r ε hproper hbdd hreg
  refine ⟨min (min l1 l3) (min l4 l5), lt_min (lt_min hl1 hl3) (lt_min hl4 hl5),
    (min_le_left _ _).trans ((min_le_left _ _).trans hl1r), fun lam hlam hlt => ?_⟩
  have lt1 : lam < l1 := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _))
  have lt3 : lam < l3 := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_right _ _))
  have lt4 : lam < l4 := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have lt5 : lam < l5 := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨W1, hW1, hW1rge, -, hW1d, L, hL⟩ := HH1 lam hlam lt1
  obtain ⟨W3, hW3, V3, hV3, -, hW3eq⟩ := H3 lam hlam lt3
  obtain ⟨W4, hW4, -, hW4c⟩ := H4 lam hlam lt4
  obtain ⟨W5, hW5, hW5s⟩ := H5 lam hlam lt5
  simp only [smul_zero, add_zero] at hW1 hW3 hW4 hW5
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun z => (moreauEnv φ lam z).toReal with hψ
  set W0 := interior (W1 ∩ W3 ∩ W4 ∩ W5) with hW0def
  have hW0 : W0 ∈ 𝓝 xbar :=
    interior_mem_nhds.2 (inter_mem (inter_mem (inter_mem hW1 hW3) hW4) hW5)
  have hW0sub : W0 ⊆ W1 ∩ W3 ∩ W4 ∩ W5 := interior_subset
  have hW0o : IsOpen W0 := isOpen_interior
  -- local description of the graph of ∇ψ
  have hloc : ∀ x ∈ W3, ∀ y ∈ V3, y = gradient ψ x ↔ y ∈ LimitingSubdiff φ (x - lam • y) := by
    intro x hx y hy
    have he := hW3eq x hx
    constructor
    · intro h
      have : y ∈ ({gradient ψ x} : Set _) := h
      rw [← he] at this; exact this.2
    · intro h
      have : y ∈ {v | v ∈ V3 ∧ v ∈ LimitingSubdiff φ (x - lam • v)} := ⟨hy, h⟩
      rw [he] at this; exact this
  have h0V3 : (0 : EuclideanSpace ℝ (Fin n)) ∈ V3 := mem_of_mem_nhds hV3
  have hxbarW3 : xbar ∈ W3 := mem_of_mem_nhds hW3
  have hψ0 : gradient ψ xbar = 0 :=
    ((hloc xbar hxbarW3 0 h0V3).2 (by simpa using hH.1)).symm
  have hzero : ∀ y ∈ W3, (0 ∈ LimitingSubdiff φ y ↔ gradient ψ y = 0) := by
    intro y hy
    have := hloc y hy 0 h0V3
    simp only [smul_zero, sub_zero] at this
    constructor
    · intro h; exact (this.2 h).symm
    · intro h; exact this.1 h.symm
  have hC : IsC11Around ψ xbar := ⟨W1, hW1, hW1d, L, hL⟩
  have hgc : ContinuousAt (gradient ψ) xbar := (hL.continuousOn).continuousAt hW1
  -- (H1) for ∇ψ
  obtain ⟨U1, hU1, V1, hV1, hH1⟩ := hH.2.1
  have hpc : ContinuousAt (fun x => x - lam • gradient ψ x) xbar :=
    continuousAt_id.sub (hgc.const_smul lam)
  have hH1ψ : H1 (sv (gradient ψ)) xbar 0 := by
    refine ⟨W0 ∩ ((fun x => x - lam • gradient ψ x) ⁻¹' U1 ∩ gradient ψ ⁻¹' (V1 ∩ V3)),
      inter_mem hW0 (inter_mem (hpc.preimage_mem_nhds (by simpa [hψ0] using hU1))
        (hgc.preimage_mem_nhds (by rw [hψ0]; exact inter_mem hV1 hV3))),
      Set.univ, univ_mem, fun x hx v _ hv => ?_⟩
    have hv' : v = gradient ψ x := hv
    subst hv'
    obtain ⟨hxW, hxU1, hxV⟩ := hx
    have hxW' := hW0sub hxW
    have hmem : gradient ψ x ∈ LimitingSubdiff φ (x - lam • gradient ψ x) :=
      (hloc x hxW'.1.1.2 _ hxV.2).1 rfl
    obtain ⟨d', hd'⟩ := hH1 _ hxU1 _ hxV.1 hmem
    refine ⟨d' - lam • gradient ψ x, ?_⟩
    rw [hW4c x hxW'.1.2]
    simp only [smul_neg, sub_neg_eq_add, sub_add_cancel]
    exact hd'
  -- (H2) for ∇ψ
  have hN : W3 ×ˢ V3 ∈ 𝓝 ((xbar, 0) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    prod_mem_nhds hW3 hV3
  have hlocq : ∀ q ∈ W3 ×ˢ V3, q ∈ gph (sv (gradient ψ)) ↔
      ((q.1 - lam • q.2, q.2) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∈
        gph (LimitingSubdiff φ) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact hloc x hx y hy
  have hMR : MetricRegularAround (sv (gradient ψ)) xbar 0 := by
    refine MR_transfer (LimitingSubdiff φ) (sv (gradient ψ)) xbar
      (lam • ContinuousLinearMap.id ℝ _) hN (fun q hq => ?_) hH.2.2.1
    rw [hlocq q hq]; simp
  -- (H3) for ∇ψ
  have hsv0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ sv (gradient ψ) xbar := by
    show (0 : EuclideanSpace ℝ (Fin n)) ∈ ({gradient ψ xbar} : Set _)
    rw [hψ0]; exact Set.mem_singleton _
  have hSS : IsSemismoothStar (sv (gradient ψ)) xbar 0 :=
    semismooth_shear (LimitingSubdiff φ) (sv (gradient ψ)) xbar lam isOpen_interior
      (mem_interior_iff_mem_nhds.2 hN)
      (fun q hq => hlocq q (interior_subset hq)) hsv0 hH.2.2.2
  have hSH : StandingH (sv (gradient ψ)) xbar 0 := ⟨hsv0, hH1ψ, hMR, hSS⟩
  -- Theorem 5.7 (localized)
  obtain ⟨U, hU, hUdef, hUconv⟩ :=
    GenNewtonSubgrad.Composite.theorem_5_7_local ψ xbar hC hψ0 hSH W0 hW0
  -- one step of Algorithm 6.2 is one step of Algorithm 5.3 for ψ on W0
  have hstep : ∀ y ∈ W0, ∀ y', alg62Step φ lam y y' ↔ alg53Step ψ y y' := by
    intro y hy y'
    have hyW := hW0sub hy
    have hz := hzero y hyW.1.1.2
    obtain ⟨hne, hR⟩ := hW5s y hyW.2
    have hp : ∀ p : EuclideanSpace ℝ (Fin n), y - lam • (lam⁻¹ • (y - p)) = p := by
      intro p; rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, sub_sub_cancel]
    constructor
    · rintro (⟨h0, rfl⟩ | ⟨h0, p, hpm, hd⟩)
      · exact Or.inl ⟨hz.1 h0, rfl⟩
      · refine Or.inr ⟨fun h => h0 (hz.2 h), ?_⟩
        obtain ⟨-, hiff, hco⟩ := hR p hpm
        rw [← hco]
        apply (hiff (y' - y)).1
        rw [hp]; exact hd
    · rintro (⟨h0, rfl⟩ | ⟨h0, hd⟩)
      · exact Or.inl ⟨hz.2 h0, rfl⟩
      · refine Or.inr ⟨fun h => h0 (hz.1 h), ?_⟩
        obtain ⟨p, hpm⟩ := hne
        obtain ⟨-, hiff, hco⟩ := hR p hpm
        refine ⟨p, hpm, ?_⟩
        rw [← hco] at hd
        have := (hiff (y' - y)).2 hd
        rwa [hp] at this
  set U' := U ∩ W0 with hU'
  have key : ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 ∈ U → ∀ N : ℕ,
      (∀ k < N, alg62Step φ lam (x k) (x (k + 1))) →
        ∀ k < N, alg53Step ψ (x k) (x (k + 1)) := by
    intro x h0 N
    induction N with
    | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
      intro hs k hk
      have ih' := ih (fun j hj => hs j (Nat.lt_succ_of_lt hj))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact ih' k hk
      · subst hk
        exact (hstep _ (hUdef k x h0 ih').1 _).1 (hs k (Nat.lt_succ_self k))
  refine ⟨U', inter_mem hU hW0, fun y hy => hW1rge (hW0sub hy.2).1.1.1, fun N x h0 hs => ?_,
    fun x hrun h0 => ?_⟩
  · obtain ⟨hxN, x', hx'⟩ := hUdef N x h0.1 (key x h0.1 N hs)
    exact ⟨x', (hstep _ hxN x').2 hx'⟩
  · exact hUconv x (fun k => key x h0.1 (k + 1) (fun j _ => hrun.2 j) k (Nat.lt_succ_self k)) h0.1
