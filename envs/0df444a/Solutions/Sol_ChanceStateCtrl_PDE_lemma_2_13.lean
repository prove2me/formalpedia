-- Prove2me | solution 1 for ChanceStateCtrl.PDE.lemma_2_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T12:29:56.000857+00:00
-- url     : https://prove2.me/submissions/bbfbc301-0e93-4ec2-8a0a-72c02a5494d7

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise
open ChanceStateCtrl.PDE

/-- Affine decomposition `S(u, z) = S(u, 0) + P(0, z)`. -/
private lemma stateS_eq {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
    (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (f₀ : L2 D) (φ : Fin m → L2 D) (u : L2 D)
    (z : EuclideanSpace ℝ (Fin m)) (x : closure D) :
    stateS Ainv f₀ φ u z x = stateS Ainv f₀ φ u 0 x + stateP Ainv φ 0 z x := by
  simp [stateS, stateP, map_add, map_sum, map_smul]

private lemma stateP_smul {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
    (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (φ : Fin m → L2 D) (r : ℝ)
    (z : EuclideanSpace ℝ (Fin m)) (x : closure D) :
    stateP Ainv φ 0 (r • z) x = r * stateP Ainv φ 0 z x := by
  simp [stateP, Finset.mul_sum, mul_assoc]

theorem solution {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosDef)
    (ubar : L2 D) (h26 : ∀ x : closure D, stateS Ainv f₀ φ ubar 0 x < α)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1)
    (hv : radius (gPDE Ainv f₀ φ α) Sigma ubar v = ⊤) :
    clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar = {0} := by

  classical
  have hne : Nonempty (closure D) := by
    obtain ⟨x, hx⟩ := hDne; exact ⟨⟨x, subset_closure hx⟩⟩
  set w := sigmaRoot Sigma (v : EuclideanSpace ℝ (Fin m)) with hw
  -- Step 1: `ρ(ū, v) = ∞` forces `P(0, Σ^{1/2} v) ≤ 0` on the closure of `D`.
  have hP : ∀ x, stateP Ainv φ 0 w x ≤ 0 := by
    intro x0
    by_contra hpos
    push_neg at hpos
    set r0 := (α - stateS Ainv f₀ φ ubar 0 x0) / stateP Ainv φ 0 w x0 + 1 with hr0
    have hlt : ENNReal.ofReal r0 < radius (gPDE Ainv f₀ φ α) Sigma ubar v := by
      rw [hv]; exact ENNReal.ofReal_lt_top
    simp only [radius] at hlt
    rw [lt_biSup_iff] at hlt
    obtain ⟨r, ⟨hr0', hr⟩, hrr⟩ := hlt
    have hrr' : r0 < r := by
      by_contra hc; push_neg at hc
      exact (not_le.2 hrr) (ENNReal.ofReal_le_ofReal hc)
    have hbdd : BddAbove (Set.range fun x : closure D => stateS Ainv f₀ φ ubar (r • w) x) :=
      (isCompact_range (stateS Ainv f₀ φ ubar (r • w)).continuous).bddAbove
    have h1 : stateS Ainv f₀ φ ubar (r • w) x0 ≤ α := by
      have := le_ciSup hbdd x0
      simp only [gPDE, sub_nonpos] at hr
      linarith
    rw [stateS_eq, stateP_smul] at h1
    have h2 : (α - stateS Ainv f₀ φ ubar 0 x0) < (r0 - 1) * stateP Ainv φ 0 w x0 + stateP Ainv φ 0 w x0 := by
      rw [hr0, add_sub_cancel_right, div_mul_cancel₀ _ hpos.ne']
      linarith
    nlinarith
  -- Step 2: a neighbourhood of `ū` on which `S(u, 0) ≤ α`.
  have hmax : ∃ x0, ∀ x, stateS Ainv f₀ φ ubar 0 x ≤ stateS Ainv f₀ φ ubar 0 x0 := by
    obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      (stateS Ainv f₀ φ ubar 0).continuous.continuousOn
    exact ⟨x0, fun x => hx0 (Set.mem_univ x)⟩
  obtain ⟨x0, hx0⟩ := hmax
  set δ := α - stateS Ainv f₀ φ ubar 0 x0 with hδ
  have hδpos : 0 < δ := by have := h26 x0; linarith
  have hN : ∀ᶠ u in 𝓝 ubar, ∀ x, stateS Ainv f₀ φ u 0 x ≤ α := by
    have hc : Continuous fun u : L2 D => stateS Ainv f₀ φ u 0 := by
      simp only [stateS]
      fun_prop
    have := (hc.tendsto ubar).eventually (Metric.ball_mem_nhds _ hδpos)
    filter_upwards [this] with u hu x
    rw [dist_comm] at hu
    have h1 := ContinuousMap.dist_apply_le_dist (f := stateS Ainv f₀ φ ubar 0)
      (g := stateS Ainv f₀ φ u 0) x
    rw [Real.dist_eq] at h1
    have h2 := hx0 x
    have h3 := (abs_le.1 (h1.trans hu.le)).1
    linarith
  -- Step 3: on that neighbourhood `e(·, v)` is constant.
  have hconst : ∀ᶠ u in 𝓝 ubar, radialProb (gPDE Ainv f₀ φ α) Sigma u v =
      (chiLaw m {r | 0 ≤ r}).toReal := by
    filter_upwards [hN] with u hu
    simp only [radialProb]
    congr 2
    ext r
    simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hr
    simp only [gPDE, sub_nonpos]
    refine ciSup_le fun x => ?_
    rw [← hw, stateS_eq, stateP_smul]
    have := hu x
    have := hP x
    nlinarith
  -- Step 4: the Clarke directional derivative vanishes.
  have hdir : ∀ h, clarkeDir (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar h = 0 := by
    intro h
    have ht : Tendsto (fun q : L2 D × ℝ => q.1 + q.2 • h) (𝓝 ubar ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 ubar) := by
      have := (tendsto_fst (f := 𝓝 ubar) (g := 𝓝[>] (0 : ℝ))).add
        (((tendsto_snd (f := 𝓝 ubar) (g := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds).smul_const h)
      simpa using this
    have h1 : ∀ᶠ q : L2 D × ℝ in 𝓝 ubar ×ˢ 𝓝[>] (0 : ℝ),
        radialProb (gPDE Ainv f₀ φ α) Sigma q.1 v = (chiLaw m {r | 0 ≤ r}).toReal :=
      tendsto_fst.eventually hconst
    have h2 := ht.eventually hconst
    have hev : (fun q : L2 D × ℝ => (radialProb (gPDE Ainv f₀ φ α) Sigma (q.1 + q.2 • h) v -
        radialProb (gPDE Ainv f₀ φ α) Sigma q.1 v) / q.2) =ᶠ[𝓝 ubar ×ˢ 𝓝[>] (0 : ℝ)]
        fun _ => (0 : ℝ) := by
      filter_upwards [h1, h2] with q hq1 hq2
      rw [hq1, hq2, sub_self, zero_div]
    simp only [clarkeDir]
    rw [limsup_congr hev, limsup_const]
  -- Step 5: hence `∂^C_u e(ū, v) = {0}`.
  ext y
  simp only [clarkeSubdiffL2, Set.mem_setOf_eq, Set.mem_singleton_iff, hdir]
  constructor
  · intro hy
    exact real_inner_self_nonpos.1 (hy y)
  · rintro rfl h
    simp
