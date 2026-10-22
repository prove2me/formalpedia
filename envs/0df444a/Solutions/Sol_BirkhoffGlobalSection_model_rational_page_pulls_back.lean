-- Prove2me | solution 1 for BirkhoffGlobalSection.model_rational_page_pulls_back
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T01:51:26.720346+00:00
-- url     : https://prove2.me/submissions/f60b661a-fad7-4713-aa8b-33ee4b295579

import Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics

open scoped ContDiff Topology
open BirkhoffGlobalSection

/-- Pull a convex-model rational page through the inverse regularization.
The order isomorphism clock transfers unbounded return times in both directions. -/
theorem solution {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (D : ConvexModelDynamics M φ)
    (γ : PeriodicOrbit φ) (P : ConvexModelRationalPage M D γ) :
    Nonempty (LiftedRationalPage φ γ) := by
  let q : Plane → Phase := M.fromModel ∘ P.page
  have hfront : ∀ y ∈ frontier M.body, y ∈ M.target := by
    intro y hy
    rw [← M.image_frontier] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact M.toModel_mapsTo (M.contains_component hs)
  have hfrom : ∀ y ∈ frontier M.body,
      M.fromModel y ∈ leftEnergyComponent μ c := by
    intro y hy
    rw [← M.image_frontier] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    rwa [M.left_inverse s (M.contains_component hs)]
  have hq : ∀ u ∈ closedUnitDisk, q u ∈ leftEnergyComponent μ c := by
    intro u hu
    exact hfrom (P.page u) (P.mapsTo u hu)
  have hright : ∀ u ∈ closedUnitDisk, M.toModel (q u) = P.page u := by
    intro u hu
    exact M.right_inverse _ (hfront _ (P.mapsTo u hu))
  have hto_inj : ∀ s ∈ leftEnergyComponent μ c,
      ∀ t ∈ leftEnergyComponent μ c, M.toModel s = M.toModel t → s = t := by
    intro s hs t ht he
    calc
      s = M.fromModel (M.toModel s) := (M.left_inverse _ (M.contains_component hs)).symm
      _ = M.fromModel (M.toModel t) := congrArg M.fromModel he
      _ = t := M.left_inverse _ (M.contains_component ht)
  have horbit : ∀ s ∈ orbitSet γ, s ∈ leftEnergyComponent μ c := by
    rintro s ⟨t, rfl⟩
    exact (φ t γ.point).property
  have hclosed : ∀ u ∈ openUnitDisk, u ∈ closedUnitDisk := by
    intro u hu
    exact le_of_lt (show planeNormSq u < 1 from hu)
  have hcircle : ∀ u ∈ unitCircle, u ∈ closedUnitDisk := by
    intro u hu
    exact le_of_eq (show planeNormSq u = 1 from hu)
  have hq_smooth : ∀ u ∈ closedUnitDisk, ContDiffAt ℝ ∞ q u := by
    intro u hu
    exact (M.fromModel_smooth.contDiffAt
      (M.target_open.mem_nhds (hfront _ (P.mapsTo u hu)))).comp u (P.smooth u hu)
  have hderiv : ∀ u ∈ closedUnitDisk, ∀ v : Plane,
      fderiv ℝ M.toModel (q u) (fderiv ℝ q u v) = fderiv ℝ P.page u v := by
    intro u hu v
    have hys := hfront _ (P.mapsTo u hu)
    have hdf : DifferentiableAt ℝ M.fromModel (P.page u) :=
      (M.fromModel_smooth.contDiffAt (M.target_open.mem_nhds hys)).differentiableAt
        (by simp)
    have hdt : DifferentiableAt ℝ M.toModel (q u) :=
      (M.toModel_smooth.contDiffAt (M.source_open.mem_nhds
        (M.contains_component (hq u hu)))).differentiableAt (by simp)
    have hdp : DifferentiableAt ℝ P.page u := (P.smooth u hu).differentiableAt (by simp)
    have hinverse : fderiv ℝ (M.toModel ∘ M.fromModel) (P.page u) =
        ContinuousLinearMap.id ℝ Phase := by
      have heq : (M.toModel ∘ M.fromModel) =ᶠ[𝓝 (P.page u)] id := by
        filter_upwards [M.target_open.mem_nhds hys] with y hy
        exact M.right_inverse y hy
      rw [heq.fderiv_eq, fderiv_id]
    have hdi : (fderiv ℝ M.toModel (q u)).comp
        (fderiv ℝ M.fromModel (P.page u)) = ContinuousLinearMap.id ℝ Phase := by
      exact (fderiv_comp (f := M.fromModel) (g := M.toModel)
        (P.page u) hdt hdf).symm.trans hinverse
    have hdq : fderiv ℝ q u = (fderiv ℝ M.fromModel (P.page u)).comp
        (fderiv ℝ P.page u) := fderiv_comp u hdf hdp
    rw [hdq]
    change ((fderiv ℝ M.toModel (q u)).comp
      (fderiv ℝ M.fromModel (P.page u))) (fderiv ℝ P.page u v) = _
    rw [hdi]
    rfl
  have hanti : ∀ u ∈ closedUnitDisk, ∀ v ∈ closedUnitDisk,
      (q u = -q v ↔ P.page u = -P.page v) := by
    intro u hu v hv
    constructor
    · intro he
      rw [← hright u hu, he, M.antipodal _ (hq v hv), hright v hv]
    · intro he
      apply hto_inj _ (hq u hu) _ ((hinv _).mp (hq v hv))
      rw [hright u hu, M.antipodal _ (hq v hv), hright v hv]
      exact he
  have hreturn : ∀ s : LeftEnergyState μ c, ∀ t : ℝ, ∀ u ∈ openUnitDisk,
      (((D.flow (D.clock s t) (M.mapState s) : ConvexModelState M) : Phase) =
          P.page u ∨
        ((D.flow (D.clock s t) (M.mapState s) : ConvexModelState M) : Phase) =
          -P.page u) →
      (((φ t s : LeftEnergyState μ c) : Phase) = q u ∨
        ((φ t s : LeftEnergyState μ c) : Phase) = -q u) := by
    intro s t u hu hh
    rw [D.conjugacy] at hh
    rcases hh with hh | hh
    · left
      apply hto_inj _ (φ t s).property _ (hq u (hclosed u hu))
      rw [hright u (hclosed u hu)]
      exact hh
    · right
      apply hto_inj _ (φ t s).property _ ((hinv _).mp (hq u (hclosed u hu)))
      rw [M.antipodal _ (hq u (hclosed u hu)), hright u (hclosed u hu)]
      exact hh
  refine ⟨⟨q, hq, hq_smooth, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u hu v hv huv
    apply P.injective hu hv
    rw [← hright u hu, ← hright v hv, huv]
  · intro u hu v w hvw
    apply P.immersion u hu
    rw [← hderiv u hu v, ← hderiv u hu w, hvw]
  · intro u hu
    rintro ⟨v, hv⟩
    have huc := hclosed u hu
    have ht : M.timeScale (q u) ≠ 0 := ne_of_gt (M.timeScale_pos _ (hq u huc))
    have hvec : fderiv ℝ P.page u v =
        M.timeScale (q u) • hamiltonianVectorField M.modelHamiltonian (P.page u) := by
      rw [← hderiv u huc v, hv, M.vectorField _ (hq u huc), hright u huc]
    apply P.transverse u hu
    refine ⟨(M.timeScale (q u))⁻¹ • v, ?_⟩
    rw [map_smul, hvec, smul_smul, inv_mul_cancel₀ ht, one_smul]
  · apply Set.Subset.antisymm
    · rintro s ⟨u, hu, rfl⟩
      have hp : P.page u ∈ M.toModel '' orbitSet γ := by
        rw [← P.boundary]
        exact ⟨u, hu, rfl⟩
      obtain ⟨s, hs, he⟩ := hp
      have hqs : q u = s := hto_inj _ (hq u (hcircle u hu)) _ (horbit s hs)
        ((hright u (hcircle u hu)).trans he.symm)
      rwa [hqs]
    · intro s hs
      have hp : M.toModel s ∈ P.page '' unitCircle := by
        rw [P.boundary]
        exact ⟨s, hs, rfl⟩
      obtain ⟨u, hu, he⟩ := hp
      refine ⟨u, hu, ?_⟩
      apply hto_inj _ (hq u (hcircle u hu)) _ (horbit s hs)
      exact (hright u (hcircle u hu)).trans he
  · intro u hu v hv
    exact (hanti u hu v hv).trans (P.antipodal_fibers u hu v hv)
  · intro s hs
    have hs' : (M.mapState s : Phase) ∉ M.toModel '' orbitSet γ := by
      rintro ⟨z, hz, he⟩
      apply hs
      have hsz : (s : Phase) = z := hto_inj _ s.property _ (horbit z hz) he.symm
      rwa [hsz]
    obtain ⟨hplus, hminus⟩ := P.returns (M.mapState s) hs'
    constructor
    · intro R
      obtain ⟨t, ht, u, hu, he⟩ := hplus (D.clock s R)
      refine ⟨(D.clock s).symm t, ?_, u, hu, ?_⟩
      · exact (D.clock s).lt_symm_apply.mpr ht
      · apply hreturn s ((D.clock s).symm t) u hu
        simpa using he
    · intro R
      obtain ⟨t, ht, u, hu, he⟩ := hminus (D.clock s R)
      refine ⟨(D.clock s).symm t, ?_, u, hu, ?_⟩
      · exact (D.clock s).symm_apply_lt.mpr ht
      · apply hreturn s ((D.clock s).symm t) u hu
        simpa using he
