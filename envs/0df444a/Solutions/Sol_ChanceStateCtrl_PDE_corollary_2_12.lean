-- Prove2me | solution 1 for ChanceStateCtrl.PDE.corollary_2_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T12:36:11.590199+00:00
-- url     : https://prove2.me/submissions/4c54bd45-f540-474c-97f7-47945367ccf7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
import Theorems.Thm_ChanceStateCtrl_General_proposition_2_6_a
import Theorems.Thm_ChanceStateCtrl_General_proposition_2_6_b
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
    (F : L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : Differentiable ℝ F)
    (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (us : L2 D) (hus : p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us)
    (h26 : ∀ x : closure D, stateS Ainv f₀ φ us 0 x < α)
    (hslater : ∃ uh : L2 D, p < probFn P ξ (gPDE Ainv f₀ φ α) uh) :
    (IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ gradient F us ∈ lam • clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) us ∧
        p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us ∧ lam * (probFn P ξ (gPDE Ainv f₀ φ α) us - p) = 0) ∧
    (IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us →
      ∃ lam : ℝ, 0 ≤ lam ∧
        gradient F us ∈ lam • aumannL2 (sphereLaw m) (fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) us) ∧
        p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us ∧ lam * (probFn P ξ (gPDE Ainv f₀ φ α) us - p) = 0) ∧
    (((∀ᵐ v ∂(sphereLaw m), (clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) us).Subsingleton) ∨
        Bornology.IsBounded {z : EuclideanSpace ℝ (Fin m) | gPDE Ainv f₀ φ α us z ≤ 0}) →
      (∃ lam : ℝ, 0 ≤ lam ∧
        gradient F us ∈ lam • aumannL2 (sphereLaw m) (fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) us) ∧
        p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us ∧ lam * (probFn P ξ (gPDE Ainv f₀ φ α) us - p) = 0) →
      IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us) := by

  classical
  set g := gPDE Ainv f₀ φ α with hg
  have hne : Nonempty (closure D) := by
    obtain ⟨x, hx⟩ := hDne; exact ⟨⟨x, subset_closure hx⟩⟩
  -- (10)
  have h10 : g us 0 < 0 := by
    have hc : IsCompact (Set.range fun x : closure D => stateS Ainv f₀ φ us 0 x) :=
      isCompact_range (stateS Ainv f₀ φ us 0).continuous
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
  have h12 : ChanceStateCtrl.General.ModerateGrowth g Sigma us ∨
      Bornology.IsBounded {z | g us z ≤ 0} :=
    Or.inl (lemma_2_10 D hDopen hDbdd hDne hd hDS Ainv hA f₀ φ α hm Sigma hSigma us)
  have hA6 := ChanceStateCtrl.General.proposition_2_6_a P ξ Sigma g hAss hconv F hFconv hFdiff
    p hp hslater us hus h10 h12
  have hB6 := ChanceStateCtrl.General.proposition_2_6_b P ξ Sigma g hAss hconv F hFconv hFdiff
    p hp hslater us hus h10 h12
  -- Riesz bridges
  have hgradE : InnerProductSpace.toDual ℝ (L2 D) (gradient F us) = fderiv ℝ F us := by
    simp [gradient]
  have hCS : ∀ y, y ∈ clarkeSubdiffL2 (probFn P ξ g) us ↔
      InnerProductSpace.toDual ℝ (L2 D) y ∈
        ChanceStateCtrl.General.clarkeSubdiff (ChanceStateCtrl.General.probFn P ξ g) us :=
    fun y => mem_clarke_iff _ us y
  have hAU : ∀ y, y ∈ aumannL2 (sphereLaw m)
      (fun v => clarkeSubdiffL2 (fun u => radialProb g Sigma u v) us) ↔
      InnerProductSpace.toDual ℝ (L2 D) y ∈ ChanceStateCtrl.General.aumann
        (ChanceStateCtrl.General.sphereLaw m)
        (fun v => ChanceStateCtrl.General.clarkeSubdiff
          (fun u => ChanceStateCtrl.General.radialProb Sigma g u v) us) :=
    fun y => mem_aumann_iff (sphereLaw m) _ _ (fun v y => mem_clarke_iff _ us y) y
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hsol
      obtain ⟨lam, hlam, ⟨x, hx, hfx⟩, hp', hcs⟩ := hA6.1 hsol
      exact ⟨lam, hlam, (smul_mem_iff _ _ hCS lam _).2 ⟨x, hx, by rw [hgradE]; exact hfx⟩, hp', hcs⟩
    · rintro ⟨lam, hlam, hmem, hp', hcs⟩
      obtain ⟨x, hx, hfx⟩ := (smul_mem_iff _ _ hCS lam _).1 hmem
      exact hA6.2 ⟨lam, hlam, ⟨x, hx, by rw [← hgradE]; exact hfx⟩, hp', hcs⟩
  · intro hsol
    obtain ⟨lam, hlam, ⟨x, hx, hfx⟩, hp', hcs⟩ := hB6.1 hsol
    exact ⟨lam, hlam, (smul_mem_iff _ _ hAU lam _).2 ⟨x, hx, by rw [hgradE]; exact hfx⟩, hp', hcs⟩
  · intro hcond hkkt
    obtain ⟨lam, hlam, hmem, hp', hcs⟩ := hkkt
    obtain ⟨x, hx, hfx⟩ := (smul_mem_iff _ _ hAU lam _).1 hmem
    refine hB6.2 ?_ ⟨lam, hlam, ⟨x, hx, by rw [← hgradE]; exact hfx⟩, hp', hcs⟩
    rcases hcond with hs | hb
    · left
      have hs' : ∀ᵐ v ∂(ChanceStateCtrl.General.sphereLaw m),
          (clarkeSubdiffL2 (fun u => radialProb g Sigma u v) us).Subsingleton := hs
      rw [← ae_iff]
      filter_upwards [hs'] with v hv
      intro x1 hx1 x2 hx2
      have e1 := (mem_clarke_iff (fun u => radialProb g Sigma u v) us
        ((InnerProductSpace.toDual ℝ (L2 D)).symm x1)).2 (by rw [LinearIsometryEquiv.apply_symm_apply]; exact hx1)
      have e2 := (mem_clarke_iff (fun u => radialProb g Sigma u v) us
        ((InnerProductSpace.toDual ℝ (L2 D)).symm x2)).2 (by rw [LinearIsometryEquiv.apply_symm_apply]; exact hx2)
      have := hv e1 e2
      simpa using congrArg (InnerProductSpace.toDual ℝ (L2 D)) this
    · right; exact hb
