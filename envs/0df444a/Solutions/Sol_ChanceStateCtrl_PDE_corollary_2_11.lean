-- Prove2me | solution 1 for ChanceStateCtrl.PDE.corollary_2_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T12:41:36.946965+00:00
-- url     : https://prove2.me/submissions/3640b594-02dd-4649-b945-238205686e26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
import Theorems.Thm_ChanceStateCtrl_General_theorem_2_2_lipschitz
import Theorems.Thm_ChanceStateCtrl_General_theorem_2_2_subdiff
import Theorems.Thm_ChanceStateCtrl_PDE_clarke_singleton_strict
import Theorems.Thm_ChanceStateCtrl_PDE_lemma_2_9
import Theorems.Thm_ChanceStateCtrl_PDE_lemma_2_10

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise
open ChanceStateCtrl.PDE

section Bridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Riesz identification of the two Clarke subdifferentials (on `H` and on `H*`). -/
private lemma mem_clarke_iff (f : H → ℝ) (u y : H) :
    y ∈ clarkeSubdiffL2 f u ↔
      InnerProductSpace.toDual ℝ H y ∈ ChanceStateCtrl.General.clarkeSubdiff f u := by
  simp only [clarkeSubdiffL2, ChanceStateCtrl.General.clarkeSubdiff, Set.mem_setOf_eq,
    InnerProductSpace.toDual_apply_apply]
  rfl

/-- Riesz identification of the two Aumann integrals. -/
private lemma mem_aumann_iff {V : Type*} [MeasurableSpace V] (μ : Measure V) (Φ : V → Set H)
    (Φ' : V → Set (StrongDual ℝ H))
    (hΦ : ∀ v y, y ∈ Φ v ↔ InnerProductSpace.toDual ℝ H y ∈ Φ' v) (y : H) :
    y ∈ aumannL2 μ Φ ↔ InnerProductSpace.toDual ℝ H y ∈ ChanceStateCtrl.General.aumann μ Φ' := by
  constructor
  · rintro ⟨s, hs, hint, heq⟩
    refine ⟨fun v => InnerProductSpace.toDual ℝ H (s v), ?_, ?_, ?_⟩
    · filter_upwards [hs] with v hv
      exact (hΦ v (s v)).1 hv
    · intro h; simpa [InnerProductSpace.toDual_apply_apply] using hint h
    · intro h; simpa [InnerProductSpace.toDual_apply_apply] using heq h
  · rintro ⟨s, hs, hint, heq⟩
    refine ⟨fun v => (InnerProductSpace.toDual ℝ H).symm (s v), ?_, ?_, ?_⟩
    · filter_upwards [hs] with v hv
      exact (hΦ v _).2 (by simpa using hv)
    · intro h
      have : (fun v => inner ℝ ((InnerProductSpace.toDual ℝ H).symm (s v)) h) = fun v => s v h := by
        funext v
        rw [InnerProductSpace.toDual_symm_apply]
      rw [this]; exact hint h
    · intro h
      have : (fun v => inner ℝ ((InnerProductSpace.toDual ℝ H).symm (s v)) h) = fun v => s v h := by
        funext v
        rw [InnerProductSpace.toDual_symm_apply]
      rw [this, ← heq h, InnerProductSpace.toDual_apply_apply]

private lemma smul_mem_iff (S : Set H) (S' : Set (StrongDual ℝ H))
    (hS : ∀ y, y ∈ S ↔ InnerProductSpace.toDual ℝ H y ∈ S') (lam : ℝ) (g : H) :
    g ∈ lam • S ↔ ∃ x ∈ S', InnerProductSpace.toDual ℝ H g = lam • x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨InnerProductSpace.toDual ℝ H y, (hS y).1 hy, by simp⟩
  · rintro ⟨x, hx, he⟩
    refine ⟨(InnerProductSpace.toDual ℝ H).symm x, (hS _).2 (by simpa using hx), ?_⟩
    apply (InnerProductSpace.toDual ℝ H).injective
    simp [he]

private lemma reflexive_of_hilbert : ChanceStateCtrl.General.IsReflexive H := by
  intro Φ
  let ψ : StrongDual ℝ H := Φ.comp
    ((InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨(InnerProductSpace.toDual ℝ H).symm ψ, ?_⟩
  ext f
  obtain ⟨w, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective f
  simp only [NormedSpace.dual_def, InnerProductSpace.toDual_apply_apply,
    InnerProductSpace.toDual_symm_apply]
  rw [real_inner_comm, ← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  rfl

end Bridge

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
    (∃ K, ∃ t ∈ 𝓝 ubar, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      LipschitzOnWith K (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) t) ∧
    LocLipschitzAt (probFn P ξ (gPDE Ainv f₀ φ α)) ubar ∧
    clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar ⊆
      aumannL2 (sphereLaw m) (fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar) ∧
    ((∀ᵐ v ∂(sphereLaw m), (clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar).Subsingleton) →
      ∃ y : L2 D, clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar = {y} ∧
        clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar =
          aumannL2 (sphereLaw m) (fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar) ∧
        ∀ h : L2 D, Tendsto (fun q : L2 D × ℝ => (probFn P ξ (gPDE Ainv f₀ φ α) (q.1 + q.2 • h) - probFn P ξ (gPDE Ainv f₀ φ α) q.1) / q.2)
          (𝓝 ubar ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ y h))) := by
  classical
  set g := gPDE Ainv f₀ φ α with hg
  have hne : Nonempty (closure D) := by
    obtain ⟨x, hx⟩ := hDne; exact ⟨⟨x, subset_closure hx⟩⟩
  -- (10)
  have h10 : g ubar 0 < 0 := by
    have hc : IsCompact (Set.range fun x : closure D => stateS Ainv f₀ φ ubar 0 x) :=
      isCompact_range (stateS Ainv f₀ φ ubar 0).continuous
    obtain ⟨x, hx⟩ := hc.sSup_mem (Set.range_nonempty _)
    simp only [hg, gPDE, sub_neg]
    rw [iSup, ← hx]
    exact h26 x
  -- Lemma 2.9
  obtain ⟨hconv, ⟨C, hLip⟩, -⟩ := lemma_2_9 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α ξ hξ
  have hGconv : ∀ u, ConvexOn ℝ Set.univ (g u) := by
    intro u
    refine ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
    have := hconv.2 (Set.mem_univ (u, z₁)) (Set.mem_univ (u, z₂)) ha hb hab
    have hpt : a • (u, z₁) + b • (u, z₂) = (u, a • z₁ + b • z₂) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst]; rw [← add_smul, hab, one_smul]
      · simp
    rw [hpt] at this
    simpa [Function.uncurry] using this
  -- Assumption 2.1 for (24)
  have hsep : TopologicalSpace.SeparableSpace (L2 D) := by
    have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
    have : SecondCountableTopology (L2 D) := Lp.SecondCountableTopology
    infer_instance
  have hAss : ChanceStateCtrl.General.Assumption21 P ξ Sigma g :=
    { complete := inferInstance
      separable := hsep
      reflexive := reflexive_of_hilbert
      isProb := inferInstance
      dim_pos := hm
      measurable_xi := hξ
      posDef := hSigma
      law := hξlaw
      locLip := hLip.locallyLipschitz
      convex_snd := hGconv }
  -- (12) from Lemma 2.10
  have h12 : ChanceStateCtrl.General.ModerateGrowth g Sigma ubar ∨
      Bornology.IsBounded {z | g ubar z ≤ 0} :=
    Or.inl (lemma_2_10 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α hm Sigma hSigma ubar)
  have hL := ChanceStateCtrl.General.theorem_2_2_lipschitz P ξ Sigma g hAss ubar h10 h12
  have hS := ChanceStateCtrl.General.theorem_2_2_subdiff P ξ Sigma g hAss ubar h10 h12
  have hCS : ∀ y, y ∈ clarkeSubdiffL2 (probFn P ξ g) ubar ↔
      InnerProductSpace.toDual ℝ (L2 D) y ∈
        ChanceStateCtrl.General.clarkeSubdiff (ChanceStateCtrl.General.probFn P ξ g) ubar :=
    fun y => mem_clarke_iff _ ubar y
  have hAU : ∀ y, y ∈ aumannL2 (sphereLaw m)
      (fun v => clarkeSubdiffL2 (fun u => radialProb g Sigma u v) ubar) ↔
      InnerProductSpace.toDual ℝ (L2 D) y ∈ ChanceStateCtrl.General.aumann
        (ChanceStateCtrl.General.sphereLaw m)
        (fun v => ChanceStateCtrl.General.clarkeSubdiff
          (fun u => ChanceStateCtrl.General.radialProb Sigma g u v) ubar) :=
    fun y => mem_aumann_iff (sphereLaw m) _ _ (fun v y => mem_clarke_iff _ ubar y) y
  have hLip : LocLipschitzAt (probFn P ξ g) ubar := hL.2
  refine ⟨hL.1, hLip, ?_, ?_⟩
  · intro y hy
    exact (hAU y).2 (hS.1 ((hCS y).1 hy))
  · intro hs
    have hs' : ∀ᵐ v ∂(ChanceStateCtrl.General.sphereLaw m),
        (clarkeSubdiffL2 (fun u => radialProb g Sigma u v) ubar).Subsingleton := hs
    have hnull : ChanceStateCtrl.General.sphereLaw m {v | ¬ (ChanceStateCtrl.General.clarkeSubdiff
        (fun u => ChanceStateCtrl.General.radialProb Sigma g u v) ubar).Subsingleton} = 0 := by
      rw [← ae_iff]
      filter_upwards [hs'] with v hv
      intro x1 hx1 x2 hx2
      have e1 := (mem_clarke_iff (fun u => radialProb g Sigma u v) ubar
        ((InnerProductSpace.toDual ℝ (L2 D)).symm x1)).2
        (by rw [LinearIsometryEquiv.apply_symm_apply]; exact hx1)
      have e2 := (mem_clarke_iff (fun u => radialProb g Sigma u v) ubar
        ((InnerProductSpace.toDual ℝ (L2 D)).symm x2)).2
        (by rw [LinearIsometryEquiv.apply_symm_apply]; exact hx2)
      have := hv e1 e2
      simpa using congrArg (InnerProductSpace.toDual ℝ (L2 D)) this
    obtain ⟨⟨x, hx⟩, heq⟩ := hS.2 hnull
    set y := (InnerProductSpace.toDual ℝ (L2 D)).symm x with hydef
    have hsing : clarkeSubdiffL2 (probFn P ξ g) ubar = {y} := by
      ext z
      rw [hCS z, Set.mem_singleton_iff]
      have hx' : ChanceStateCtrl.General.clarkeSubdiff (ChanceStateCtrl.General.probFn P ξ g) ubar
          = {x} := hx
      rw [hx', Set.mem_singleton_iff, hydef]
      constructor
      · intro hz; rw [← hz]; simp
      · intro hz; rw [hz]; simp
    refine ⟨y, hsing, ?_, ?_⟩
    · ext z
      rw [hCS z, hAU z]
      have heq' : ChanceStateCtrl.General.clarkeSubdiff (ChanceStateCtrl.General.probFn P ξ g) ubar
          = ChanceStateCtrl.General.aumann (ChanceStateCtrl.General.sphereLaw m)
            (fun v => ChanceStateCtrl.General.clarkeSubdiff
              (fun u => ChanceStateCtrl.General.radialProb Sigma g u v) ubar) := heq
      rw [heq']
    · intro h
      exact clarke_singleton_strict (probFn P ξ g) ubar y hLip hsing h
