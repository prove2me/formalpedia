-- Prove2me | solution 1 for ChanceStateCtrl.PDE.theorem_2_15
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T12:30:14.808232+00:00
-- url     : https://prove2.me/submissions/b79f9986-1739-49ca-8de5-7cc9bf036b4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model
import Theorems.Thm_ChanceStateCtrl_PDE_corollary_2_11
import Theorems.Thm_ChanceStateCtrl_PDE_lemma_2_13
import Theorems.Thm_ChanceStateCtrl_PDE_lemma_2_14
import Theorems.Thm_ChanceStateCtrl_PDE_lemma_2_9
import Theorems.Thm_ChanceStateCtrl_PDE_theorem_2_4_bounded

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise
open ChanceStateCtrl.PDE

/-- Splitting an Aumann integral along a measurable set `R`: on `Rᶜ` the integrand is `{0}`, on `R`
it is `-Φ`. -/
private lemma aumann_split {V H : Type*} [MeasurableSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (μ : Measure V) (R : Set V) (hR : MeasurableSet R)
    (Ψ Φ : V → Set H) (h1 : ∀ v, v ∉ R → Ψ v = {0}) (h2 : ∀ v, v ∈ R → Ψ v = -Φ v) :
    aumannL2 μ Ψ = -aumannL2 (μ.restrict R) Φ := by
  ext x
  rw [Set.mem_neg]
  constructor
  · rintro ⟨s, hs, hint, heq⟩
    refine ⟨fun v => -s v, ?_, ?_, ?_⟩
    · rw [ae_restrict_iff' hR]
      filter_upwards [hs] with v hv hvR
      rw [h2 v hvR, Set.mem_neg] at hv
      exact hv
    · intro h
      simpa [inner_neg_left] using ((hint h).neg).restrict (s := R)
    · intro h
      have hz : ∀ᵐ v ∂μ, v ∉ R → inner ℝ (s v) h = 0 := by
        filter_upwards [hs] with v hv hvR
        rw [h1 v hvR, Set.mem_singleton_iff] at hv
        simp [hv]
      rw [inner_neg_left, heq h, ← setIntegral_eq_integral_of_ae_compl_eq_zero hz]
      simp only [inner_neg_left]
      rw [integral_neg]
  · rintro ⟨s, hs, hint, heq⟩
    refine ⟨R.indicator (fun v => -s v), ?_, ?_, ?_⟩
    · have hs' := (ae_restrict_iff' hR).1 hs
      filter_upwards [hs'] with v hv
      by_cases hvR : v ∈ R
      · rw [Set.indicator_of_mem hvR, h2 v hvR, Set.mem_neg, neg_neg]
        exact hv hvR
      · rw [Set.indicator_of_notMem hvR, h1 v hvR]
        rfl
    · intro h
      have : (fun v => inner ℝ (R.indicator (fun v => -s v) v) h) =
          R.indicator (fun v => -inner ℝ (s v) h) := by
        funext v
        by_cases hvR : v ∈ R
        · simp [Set.indicator_of_mem hvR, inner_neg_left]
        · simp [Set.indicator_of_notMem hvR]
      rw [this, integrable_indicator_iff hR]
      exact (hint h).neg
    · intro h
      have : (fun v => inner ℝ (R.indicator (fun v => -s v) v) h) =
          R.indicator (fun v => -inner ℝ (s v) h) := by
        funext v
        by_cases hvR : v ∈ R
        · simp [Set.indicator_of_mem hvR, inner_neg_left]
        · simp [Set.indicator_of_notMem hvR]
      rw [this, integral_indicator hR, integral_neg, ← heq h, inner_neg_left, neg_neg]


/-- For a function `g` convex in `z` with `g 0 < 0`, the radius along `w` is infinite iff
`g (q • w) ≤ 0` for every rational `q ≥ 0`. -/
private lemma radius_top_iff {E : Type*} [AddCommGroup E] [Module ℝ E] (G : E → ℝ)
    (hG : ConvexOn ℝ Set.univ G) (hG0 : G 0 < 0) (w : E) :
    (⨆ r ∈ {r : ℝ | 0 ≤ r ∧ G (r • w) ≤ 0}, ENNReal.ofReal r) = ⊤ ↔
      ∀ q : ℚ, 0 ≤ (q : ℝ) → G ((q : ℝ) • w) ≤ 0 := by
  constructor
  · intro htop q hq
    have hlt : ENNReal.ofReal q < ⨆ r ∈ {r : ℝ | 0 ≤ r ∧ G (r • w) ≤ 0}, ENNReal.ofReal r := by
      rw [htop]; exact ENNReal.ofReal_lt_top
    rw [lt_biSup_iff] at hlt
    obtain ⟨r, ⟨hr0, hr⟩, hqr⟩ := hlt
    have hqr' : (q : ℝ) < r := (ENNReal.ofReal_lt_ofReal_iff'.1 hqr).1
    have hrpos : 0 < r := lt_of_le_of_lt hq hqr'
    have key := hG.le_on_segment' (Set.mem_univ (0 : E)) (Set.mem_univ (r • w))
      (a := 1 - q / r) (b := q / r) (by
        rw [sub_nonneg, div_le_one hrpos]; exact hqr'.le) (div_nonneg hq hrpos.le) (by ring)
    have hpt : (1 - (q : ℝ) / r) • (0 : E) + ((q : ℝ) / r) • (r • w) = (q : ℝ) • w := by
      rw [smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ hrpos.ne']
    rw [hpt] at key
    exact key.trans (max_le hG0.le hr)
  · intro h
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    have hn := h (⌈(r : ℝ)⌉₊ : ℚ) (by positivity)
    have hle : ((⌈(r : ℝ)⌉₊ : ℚ) : ℝ) ∈ {r : ℝ | 0 ≤ r ∧ G (r • w) ≤ 0} := ⟨by positivity, hn⟩
    refine le_trans ?_ (le_biSup (fun r : ℝ => ENNReal.ofReal r) hle)
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    exact Nat.le_ceil _


theorem solution {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosDef)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hξlaw : P.map ξ = multivariateGaussian 0 Sigma)
    (ubar : L2 D) (h26 : ∀ x : closure D, stateS Ainv f₀ φ ubar 0 x < α) :
    LocLipschitzAt (probFn P ξ (gPDE Ainv f₀ φ α)) ubar ∧
    clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar ⊆ -integralSet Ainv f₀ φ α Sigma ubar ∧
    (EqCond Ainv f₀ φ α Sigma ubar → clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar = -integralSet Ainv f₀ φ α Sigma ubar) := by
  -- (10): `g(ū, 0) < 0`
  have hne : Nonempty (closure D) := by
    obtain ⟨x, hx⟩ := hDne; exact ⟨⟨x, subset_closure hx⟩⟩
  have hg0 : gPDE Ainv f₀ φ α ubar 0 < 0 := by
    have hc : IsCompact (Set.range fun x : closure D => stateS Ainv f₀ φ ubar 0 x) :=
      isCompact_range (stateS Ainv f₀ φ ubar 0).continuous
    obtain ⟨x, hx⟩ := hc.sSup_mem (Set.range_nonempty _)
    simp only [gPDE, sub_neg]
    rw [iSup, ← hx]
    exact h26 x
  -- convexity and continuity of `g(ū, ·)` (Lemma 2.9)
  obtain ⟨hconv, ⟨C, hLip⟩, -⟩ := lemma_2_9 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α ξ hξ
  have hGconv : ConvexOn ℝ Set.univ (gPDE Ainv f₀ φ α ubar) := by
    refine ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
    have := hconv.2 (Set.mem_univ (ubar, z₁)) (Set.mem_univ (ubar, z₂)) ha hb hab
    have hpt : a • (ubar, z₁) + b • (ubar, z₂) = (ubar, a • z₁ + b • z₂) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst]; rw [← add_smul, hab, one_smul]
      · simp
    rw [hpt] at this
    simpa [Function.uncurry] using this
  have hGcont : Continuous (gPDE Ainv f₀ φ α ubar) := by
    have h1 : Continuous (fun z : EuclideanSpace ℝ (Fin m) => ((ubar, z) : L2 D × _)) :=
      continuous_const.prodMk continuous_id
    have h2 := hLip.continuous.comp h1
    exact h2
  -- measurability of `R = {v | ρ(ū, v) < ∞}`
  obtain ⟨R, hRdef⟩ : ∃ R : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1),
      R = {v | radius (gPDE Ainv f₀ φ α) Sigma ubar v < ⊤} := ⟨_, rfl⟩
  have hRc : Rᶜ = ⋂ q : ℚ, {v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 |
      0 ≤ (q : ℝ) → gPDE Ainv f₀ φ α ubar ((q : ℝ) • sigmaRoot Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} := by
    ext v
    simp only [hRdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, top_le_iff, Set.mem_iInter]
    exact radius_top_iff (gPDE Ainv f₀ φ α ubar) hGconv hg0 _
  have hR : MeasurableSet R := by
    rw [← compl_compl R, hRc]
    refine MeasurableSet.compl (MeasurableSet.iInter fun q => ?_)
    by_cases hq : 0 ≤ (q : ℝ)
    · simp only [hq, true_implies]
      have hc : Continuous (fun v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          gPDE Ainv f₀ φ α ubar ((q : ℝ) • sigmaRoot Sigma (v : EuclideanSpace ℝ (Fin m)))) :=
        hGcont.comp (((sigmaRoot Sigma).continuous.comp continuous_subtype_val).const_smul (q : ℝ))
      exact (isClosed_le hc continuous_const).measurableSet
    · simp [hq]
  -- the integrand: Lemmas 2.13 and 2.14
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → Set (L2 D),
      Ψ = fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar :=
    ⟨_, rfl⟩
  have h1 : ∀ v, v ∉ R → Ψ v = {0} := by
    intro v hv
    simp only [hRdef, Set.mem_ofPred_eq, not_lt, top_le_iff] at hv
    rw [hΨ]
    exact lemma_2_13 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α hm Sigma hSigma ubar h26 v hv
  have h2 : ∀ v, v ∈ R → Ψ v = -((fun v => chiDensity m (radius (gPDE Ainv f₀ φ α) Sigma ubar v).toReal •
      Kset Ainv f₀ φ α Sigma ubar v) v) := by
    intro v hv
    rw [hRdef] at hv
    rw [hΨ]
    dsimp only
    rw [lemma_2_14 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α hm Sigma hSigma ubar h26 v hv,
      Set.neg_smul_set]
  have hsplit : aumannL2 (sphereLaw m) (fun v => clarkeSubdiffL2
      (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar) =
      -integralSet Ainv f₀ φ α Sigma ubar := by
    rw [← hΨ, integralSet, ← hRdef]
    exact aumann_split (sphereLaw m) R hR Ψ _ h1 h2
  have h211 := corollary_2_11 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α hm Sigma hSigma P ξ hξ
    hξlaw ubar h26
  refine ⟨h211.2.1, hsplit ▸ h211.2.2.1, ?_⟩
  rintro (hsing | hbdd)
  · have hsub : ∀ᵐ v ∂(sphereLaw m),
        (clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar).Subsingleton := by
      filter_upwards [hsing] with v hv
      rw [hΨ] at h1 h2
      by_cases hvR : v ∈ R
      · obtain ⟨x, hx⟩ := hv (by rw [hRdef] at hvR; exact hvR)
        have e := h2 v hvR
        dsimp only at e
        rw [e]
        simp only [Kset, hx, Set.image_singleton, convexHull_singleton, closure_singleton,
          Set.smul_set_singleton, Set.neg_singleton]
        exact Set.subsingleton_singleton
      · have e := h1 v hvR
        dsimp only at e
        rw [e]; exact Set.subsingleton_singleton
    obtain ⟨y, -, hy, -⟩ := h211.2.2.2 hsub
    rw [← hsplit]
    exact hy
  · rw [← hsplit]
    exact theorem_2_4_bounded D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α hm Sigma hSigma P ξ hξ
      hξlaw ubar h26 hbdd
