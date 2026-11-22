-- Prove2me | solution 1 for Barycenter.exists_regular_probabilityMeasure_of_mem_closure_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:56:18.882566+00:00
-- url     : https://prove2.me/submissions/5f213f73-fa8a-43d6-9100-e47643355454

import Mathlib

open Topology MeasureTheory
set_option autoImplicit false

theorem solution {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E] {K : Set E} (hK : IsCompact K) {x : E}
    (hx : x ∈ closure (convexHull ℝ K)) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ ℓ : StrongDual 𝕜 E,
        Integrable (fun y : K => ℓ (y : E)) μ ∧ ∫ y : K, ℓ (y : E) ∂μ = ℓ x := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- the restriction of a continuous linear form to `K`, as a bounded continuous function
  let f (ℓ : StrongDual 𝕜 E) : BoundedContinuousFunction K 𝕜 :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun y ↦ ℓ y.val, ℓ.continuous.comp continuous_subtype_val⟩
  -- the moment map `p ↦ (ℓ ↦ ∫ ℓ dp)` on the compact space of Borel probability measures on `K`
  let moments (p : ProbabilityMeasure K) (ℓ : StrongDual 𝕜 E) : 𝕜 :=
    ∫ y, f ℓ y ∂(p : Measure K)
  have hmoments : Continuous moments := by
    apply continuous_pi
    intro ℓ
    rw [continuous_iff_continuousAt]
    intro p
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).mp
      (Filter.tendsto_id (x := 𝓝 p)) (f ℓ)
  have hconvex : Convex ℝ (Set.range moments) := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ a b ha hb hab
    let μ := ENNReal.ofReal a • (p : Measure K)
    let ν := ENNReal.ofReal b • (q : Measure K)
    let r : ProbabilityMeasure K := ⟨μ + ν, ⟨by
      simp [μ, ν, ← ENNReal.ofReal_add ha hb, hab]⟩⟩
    refine ⟨r, ?_⟩
    funext ℓ
    change ∫ y, f ℓ y ∂(μ + ν) = a • moments p ℓ + b • moments q ℓ
    rw [integral_add_measure
      (((f ℓ).integrable (μ := (p : Measure K))).smul_measure ENNReal.ofReal_ne_top)
      (((f ℓ).integrable (μ := (q : Measure K))).smul_measure ENNReal.ofReal_ne_top)]
    simp [moments, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
  -- evaluation `z ↦ (ℓ ↦ ℓ z)`, a continuous real-linear map into the product space
  let eval : E →ₗ[ℝ] (StrongDual 𝕜 E → 𝕜) :=
    { toFun := fun z ℓ ↦ ℓ z
      map_add' := fun z w ↦ funext fun ℓ ↦ ℓ.map_add z w
      map_smul' := fun c z ↦ funext fun ℓ ↦ (ℓ.restrictScalars ℝ).map_smul c z }
  have heval : Continuous eval := continuous_pi fun ℓ ↦ ℓ.continuous
  -- the set of points represented by probability measures is closed, convex and contains `K`
  have hclosed : IsClosed (eval ⁻¹' Set.range moments) :=
    (isCompact_range hmoments).isClosed.preimage heval
  have hsubset : K ⊆ eval ⁻¹' Set.range moments := by
    intro y hy
    refine ⟨⟨Measure.dirac ⟨y, hy⟩, Measure.dirac.isProbabilityMeasure⟩, ?_⟩
    funext ℓ
    exact integral_dirac (f ℓ) ⟨y, hy⟩
  obtain ⟨p, hp⟩ :=
    closure_minimal (convexHull_min hsubset (hconvex.linear_preimage eval)) hclosed hx
  -- replace `p` by a regular measure with the same integrals of continuous functions
  obtain ⟨ν, hνreg, hνfin, hν⟩ := Measure.exists_regular_eq_of_compactSpace (p : Measure K)
  have hν1 : ν Set.univ = 1 := by
    apply (ENNReal.toReal_eq_one_iff _).mp
    simpa [measureReal_def] using (hν (1 : BoundedContinuousFunction K ℝ)).symm
  refine ⟨ν, ⟨hν1⟩, hνreg, fun ℓ ↦ ?_⟩
  have hpint := (f ℓ).integrable (μ := (p : Measure K))
  have hνint := (f ℓ).integrable (μ := ν)
  refine ⟨hνint, ?_⟩
  calc
    ∫ y, f ℓ y ∂ν = ∫ y, f ℓ y ∂(p : Measure K) := by
        apply RCLike.ext
        · let g := BoundedContinuousFunction.mkOfCompact
            ⟨fun y ↦ RCLike.re (f ℓ y), RCLike.continuous_re.comp (f ℓ).continuous⟩
          exact (integral_re hνint).symm.trans ((hν g).symm.trans (integral_re hpint))
        · let g := BoundedContinuousFunction.mkOfCompact
            ⟨fun y ↦ RCLike.im (f ℓ y), RCLike.continuous_im.comp (f ℓ).continuous⟩
          exact (integral_im hνint).symm.trans ((hν g).symm.trans (integral_im hpint))
    _ = ℓ x := congrFun hp ℓ
