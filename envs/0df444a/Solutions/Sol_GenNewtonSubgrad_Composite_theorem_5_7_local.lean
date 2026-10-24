-- Prove2me | solution 1 for GenNewtonSubgrad.Composite.theorem_5_7_local
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:25:41.688447+00:00
-- url     : https://prove2.me/submissions/c0b5ccab-d57a-4d66-8328-904b014b8b90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_5_4
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_5_5
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_5_6
import Theorems.Thm_GenNewtonSubgrad_ProxReg_scalarization_2_11

open Filter Topology
open scoped InnerProductSpace Pointwise

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


namespace GNC57
open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNC73 GNC75

variable {n : ℕ}

lemma gradient_neg' (φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => -φ y) x = -gradient φ x := by
  unfold gradient
  rw [fderiv_fun_neg, map_neg]

/-- negating a single-valued map flips the coderivative direction -/
lemma coderiv_neg_mem (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x u w : EuclideanSpace ℝ (Fin n)) :
    u ∈ coderiv (sv (fun y => -F y)) x (-F x) w → u ∈ coderiv (sv F) x (F x) (-w) := by
  intro h
  set Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) := fun q => (q.1, -q.2) with hΦ
  set Λ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (ContinuousLinearMap.fst ℝ _ _).prod (-(ContinuousLinearMap.snd ℝ _ _)) with hΛ
  have h1 : ((u, -w) : _ × _) ∈ limNormal (gph (sv (fun y => -F y))) (Φ (x, F x)) := h
  have h2 := limN_gen Φ Φ Λ (fun a b => by
      simp only [hΦ, hΛ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.neg_apply, Prod.mk_sub_mk, Prod.fst_sub,
        Prod.snd_sub, neg_sub_neg]
      refine Prod.ext rfl ?_; simp only; abel)
    Φ (fun a h => by
      simp only [pairInner, hΦ, hΛ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.neg_apply, inner_neg_left,
        inner_neg_right])
    (by simp only [hΦ]; fun_prop) (by simp only [hΦ]; fun_prop)
    (fun q => by simp [hΦ]) (S := gph (sv F)) (S' := gph (sv (fun y => -F y)))
    (fun q hq => by
      show -q.2 ∈ ({-F q.1} : Set _)
      have : q.2 = F q.1 := hq
      rw [this]; exact Set.mem_singleton _)
    (fun q hq => by
      show -q.2 ∈ ({F q.1} : Set _)
      have : q.2 = -F q.1 := hq
      rw [this, neg_neg]; exact Set.mem_singleton _)
    (show ((x, F x) : _ × _) ∈ gph (sv F) from Set.mem_singleton _) (by simp [hΦ]) h1
  have e : Φ ((u, -w) : _ × _) = (u, -(-w)) := by simp [hΦ]
  rw [e] at h2
  exact h2

lemma semismooth_neg (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (h : IsSemismoothStar (sv F) x (F x)) :
    IsSemismoothStar (sv (fun y => -F y)) x (-F x) := by
  rw [semismooth_iff_SSet] at h ⊢
  refine ⟨Set.mem_singleton _, ?_⟩
  set Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) := fun q => (q.1, -q.2) with hΦ
  set Λ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (ContinuousLinearMap.fst ℝ _ _).prod (-(ContinuousLinearMap.snd ℝ _ _)) with hΛ
  have := SSet_transfer Φ Φ Λ Λ (fun a b => by
      simp only [hΦ, hΛ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.neg_apply, Prod.mk_sub_mk, Prod.fst_sub,
        Prod.snd_sub, neg_sub_neg]
      refine Prod.ext rfl ?_; simp only; abel)
    (fun w => by simp [hΛ])
    Φ (fun a h => by
      simp only [pairInner, hΦ, hΛ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.neg_apply, inner_neg_left,
        inner_neg_right])
    (by simp only [hΦ]; fun_prop)
    (fun q => by simp [hΦ]) (S := gph (sv F)) (S' := gph (sv (fun y => -F y)))
    (fun q hq => by
      show -q.2 ∈ ({-F q.1} : Set _)
      have : q.2 = F q.1 := hq
      rw [this]; exact Set.mem_singleton _)
    (fun q hq => by
      show -q.2 ∈ ({F q.1} : Set _)
      have : q.2 = -F q.1 := hq
      rw [this, neg_neg]; exact Set.mem_singleton _)
    (show ((x, F x) : _ × _) ∈ gph (sv F) from Set.mem_singleton _) h.2
  simpa [hΦ] using this

lemma coderiv_neg_mem' (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x u w : EuclideanSpace ℝ (Fin n)) :
    u ∈ coderiv (sv F) x (F x) w → u ∈ coderiv (sv (fun y => -F y)) x (-F x) (-w) := by
  intro h
  have h' : u ∈ coderiv (sv (fun y => -(-F y))) x (-(-F x)) w := by
    simpa using h
  exact coderiv_neg_mem (fun y => -F y) x u w h'

end GNC57


open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNC73 GNC75 GNC57 in
theorem solution {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n))
    (hC11 : GenNewtonSubgrad.ProxReg.IsC11Around φ xbar) (hsol : gradient φ xbar = 0)
    (hH : GenNewtonSubgrad.ProxReg.StandingH (GenNewtonSubgrad.ProxReg.sv (gradient φ)) xbar 0) :
    ∀ V ∈ 𝓝 xbar, ∃ U ∈ 𝓝 xbar,
      (∀ (N : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin n)), x 0 ∈ U →
        (∀ k < N, GenNewtonSubgrad.ProxReg.alg53Step φ (x k) (x (k + 1))) →
          x N ∈ V ∧ ∃ x', GenNewtonSubgrad.ProxReg.alg53Step φ (x N) x') ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), GenNewtonSubgrad.ProxReg.IsAlg53Run φ x → x 0 ∈ U →
        GenNewtonSubgrad.ProxReg.IsQSuperlinear x xbar := by
  classical
  obtain ⟨-, hH1, hMR, hSS⟩ := hH
  obtain ⟨U0, hU0, hdiff0, L, hL⟩ := hC11
  -- open Lipschitz ball
  obtain ⟨r0, hr0, hball0⟩ := Metric.mem_nhds_iff.1 hU0
  have hLip : ∀ x ∈ Metric.ball xbar r0, ∃ U ∈ 𝓝 x, ∃ L', LipschitzOnWith L' (gradient φ) U :=
    fun x hx => ⟨Metric.ball xbar r0, Metric.isOpen_ball.mem_nhds hx, L, hL.mono hball0⟩
  have hgc : ContinuousAt (gradient φ) xbar :=
    (hL.continuousOn).continuousAt hU0
  -- Lemma 5.4
  obtain ⟨c, hc, U4, hU4, h54⟩ := (lemma_5_4 (gradient φ) xbar
    ⟨U0, hU0, hL.continuousOn⟩).1 (by rw [hsol]; exact hMR)
  -- Lemma 5.5 for -φ
  have hC11n : IsC11Around (fun y => -φ y) xbar := by
    refine ⟨U0, hU0, fun x hx => (hdiff0 x hx).neg, L, ?_⟩
    have : gradient (fun y => -φ y) = fun y => -gradient φ y := funext (gradient_neg' φ)
    rw [this]; exact hL.neg
  have hgn : gradient (fun y => -φ y) = fun y => -gradient φ y := funext (gradient_neg' φ)
  have hSSn : IsSemismoothStar (sv (gradient (fun y => -φ y))) xbar
      (gradient (fun y => -φ y) xbar) := by
    rw [hgn]
    exact semismooth_neg (gradient φ) xbar (by rw [hsol]; exact hSS)
  have h55 := (lemma_5_5 (fun y => -φ y) xbar hC11n).1 hSSn
  -- key estimate for directions x̄ - x
  have hb : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.closedBall xbar δ,
      ∀ b ∈ coderiv (sv (gradient φ)) x (gradient φ x) (xbar - x),
        ‖-gradient φ x - b‖ ≤ ε * ‖x - xbar‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hδP⟩ := h55 ε hε
    refine ⟨δ, hδ, fun x hx b hbm => ?_⟩
    have hbm' : b ∈ coderiv (sv (gradient (fun y => -φ y))) x
        (gradient (fun y => -φ y) x) (x - xbar) := by
      rw [hgn]
      have := coderiv_neg_mem' (gradient φ) x b (xbar - x) hbm
      simpa using this
    have := hδP x hx b hbm'
    rw [hgn] at this
    simpa [hsol] using this
  -- H1 data
  obtain ⟨U1, hU1, V1, hV1, hH1'⟩ := hH1
  obtain ⟨r1, hr1, hball1⟩ := Metric.mem_nhds_iff.1 hU1
  obtain ⟨r4, hr4, hball4⟩ := Metric.mem_nhds_iff.1 hU4
  have hscal : ∀ x ∈ Metric.ball xbar r0, ∀ d : EuclideanSpace ℝ (Fin n),
      -gradient φ x ∈ coderiv (sv (gradient φ)) x (gradient φ x) d ↔
      -gradient φ x ∈ LimitingSubdiff (fun z => ((⟪d, gradient φ z⟫_ℝ : ℝ) : EReal)) x := by
    intro x hx d
    rw [scalarization_2_11 (gradient φ) x (hLip x hx) d]
  -- one-step estimate
  have hstep : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.ball xbar δ,
      ∀ x', alg53Step φ x x' → ‖x' - xbar‖ ≤ ε * ‖x - xbar‖ := by
    intro ε hε
    obtain ⟨δ1, hδ1, hb1⟩ := hb (c * ε) (by positivity)
    obtain ⟨δ2, hδ2, hb2⟩ := hb (c / 2) (by positivity)
    set δ := min δ1 (min δ2 (min r0 (min r1 r4))) with hδdef
    have e1 : δ ≤ δ1 := min_le_left _ _
    have e2 : δ ≤ δ2 := (min_le_right _ _).trans (min_le_left _ _)
    have e3 : δ ≤ r0 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have e4 : δ ≤ r1 := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have e5 : δ ≤ r4 := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨δ, lt_min hδ1 (lt_min hδ2 (lt_min hr0 (lt_min hr1 hr4))), fun x hx x' hstp => ?_⟩
    rw [Metric.mem_ball] at hx
    have hx1 : x ∈ Metric.closedBall xbar δ1 := Metric.mem_closedBall.2 (by linarith)
    have hx2 : x ∈ Metric.closedBall xbar δ2 := Metric.mem_closedBall.2 (by linarith)
    have hxr0 : x ∈ Metric.ball xbar r0 := Metric.mem_ball.2 (by linarith)
    have hxU1 : x ∈ U1 := hball1 (Metric.mem_ball.2 (by linarith))
    have hxU4 : x ∈ U4 := hball4 (Metric.mem_ball.2 (by linarith))
    rcases hstp with ⟨h0, hxx⟩ | ⟨hne, hin⟩
    · -- stopped: then x = xbar
      have hv : gradient φ x ∈ V1 := by rw [h0]; exact mem_of_mem_nhds hV1
      obtain ⟨d, hd⟩ := hH1' x hxU1 (gradient φ x) hv (Set.mem_singleton _)
      have hd0 : d = 0 := by
        have := h54 x hxU4 d _ hd
        rw [h0, neg_zero, norm_zero] at this
        have : ‖d‖ ≤ 0 := by nlinarith [norm_nonneg d]
        exact norm_le_zero_iff.1 this
      have hmem : -gradient φ x ∈ coderiv (sv (gradient φ)) x (gradient φ x)
          ((x - xbar) + (xbar - x)) := by
        rw [show (x - xbar) + (xbar - x) = 0 by abel, ← hd0]; exact hd
      obtain ⟨a, ha, b', hb', hab⟩ := Set.mem_add.1 (lemma_5_6 (gradient φ) x (hLip x hxr0) _ _ hmem)
      have h1 := h54 x hxU4 _ a ha
      have h2 := hb2 x hx2 b' hb'
      rw [h0, neg_zero, zero_sub, norm_neg] at h2
      have hab' : a = -b' := by rw [h0, neg_zero] at hab; exact eq_neg_of_add_eq_zero_left hab
      rw [hab', norm_neg] at h1
      have hz : ‖x - xbar‖ = 0 := by nlinarith [norm_nonneg (x - xbar)]
      rw [hxx, hz, mul_zero]
    · have hin' := (hscal x hxr0 (x' - x)).2 hin
      have hsplit : x' - x = (x' - xbar) + (xbar - x) := by abel
      rw [hsplit] at hin'
      obtain ⟨a, ha, b', hb', hab⟩ := Set.mem_add.1 (lemma_5_6 (gradient φ) x (hLip x hxr0) _ _ hin')
      have h1 := h54 x hxU4 _ a ha
      have h2 := hb1 x hx1 b' hb'
      have ha' : a = -gradient φ x - b' := by rw [← hab]; abel
      rw [ha'] at h1
      have : c * ‖x' - xbar‖ ≤ c * (ε * ‖x - xbar‖) := by linarith
      exact le_of_mul_le_mul_left this hc
  -- existence of a step
  have hgV : gradient φ ⁻¹' V1 ∈ 𝓝 xbar := hgc.preimage_mem_nhds (by rw [hsol]; exact hV1)
  obtain ⟨re, hre, hballe⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hgV hU1)
  have hexist : ∀ x ∈ Metric.ball xbar (min re r0), ∃ x', alg53Step φ x x' := by
    intro x hx
    have hxe : x ∈ Metric.ball xbar re := Metric.ball_subset_ball (min_le_left _ _) hx
    have hxr0 : x ∈ Metric.ball xbar r0 := Metric.ball_subset_ball (min_le_right _ _) hx
    obtain ⟨hxV, hxU1⟩ := hballe hxe
    by_cases h0 : gradient φ x = 0
    · exact ⟨x, Or.inl ⟨h0, rfl⟩⟩
    · obtain ⟨d, hd⟩ := hH1' x hxU1 (gradient φ x) hxV (Set.mem_singleton _)
      refine ⟨x + d, Or.inr ⟨h0, ?_⟩⟩
      rw [add_sub_cancel_left]
      exact (hscal x hxr0 d).1 hd
  -- assemble
  intro V hV
  obtain ⟨rV, hrV, hballV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨δh, hδh, hδhP⟩ := hstep (1 / 2) (by norm_num)
  set r := min rV (min δh (min re r0)) with hr
  have hrpos : 0 < r := lt_min hrV (lt_min hδh (lt_min hre hr0))
  have hrV' : r ≤ rV := min_le_left _ _
  have hrδ : r ≤ δh := (min_le_right _ _).trans (min_le_left _ _)
  have hre' : r ≤ min re r0 := (min_le_right _ _).trans (min_le_right _ _)
  -- invariance of the ball
  have hinv : ∀ x x' : EuclideanSpace ℝ (Fin n), x ∈ Metric.ball xbar r → alg53Step φ x x' →
      x' ∈ Metric.ball xbar r ∧ ‖x' - xbar‖ ≤ 1 / 2 * ‖x - xbar‖ := by
    intro x x' hx hs
    have hxδ : x ∈ Metric.ball xbar δh := Metric.ball_subset_ball hrδ hx
    have h := hδhP x hxδ x' hs
    refine ⟨?_, h⟩
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    have := norm_nonneg (x - xbar)
    linarith
  have hrun : ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)), x 0 ∈ Metric.ball xbar r → ∀ N : ℕ,
      (∀ k < N, alg53Step φ (x k) (x (k + 1))) → x N ∈ Metric.ball xbar r := by
    intro x h0 N
    induction N with
    | zero => intro _; exact h0
    | succ N ih =>
      intro hs
      exact (hinv _ _ (ih (fun k hk => hs k (Nat.lt_succ_of_lt hk))) (hs N (Nat.lt_succ_self N))).1
  refine ⟨Metric.ball xbar r, Metric.ball_mem_nhds _ hrpos, fun N x h0 hs => ?_,
    fun x hx h0 => ?_⟩
  · have hN := hrun x h0 N hs
    exact ⟨hballV (Metric.ball_subset_ball hrV' hN),
      hexist _ (Metric.ball_subset_ball hre' hN)⟩
  · have hall : ∀ k, x k ∈ Metric.ball xbar r := fun k =>
      hrun x h0 k (fun j _ => hx j)
    have hgeo : ∀ k, ‖x k - xbar‖ ≤ (1 / 2) ^ k * ‖x 0 - xbar‖ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := (hinv _ _ (hall k) (hx k)).2
        rw [pow_succ]
        nlinarith
    have hconv : Tendsto x atTop (𝓝 xbar) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) hgeo ?_
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖x 0 - xbar‖
      simpa using this
    refine ⟨hconv, fun ε hε => ?_⟩
    obtain ⟨δε, hδε, hδεP⟩ := hstep ε hε
    filter_upwards [hconv.eventually (Metric.ball_mem_nhds xbar hδε)] with k hk
    exact hδεP _ hk _ (hx k)
