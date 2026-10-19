-- Prove2me | solution 1 for FlatlyFoliated.orthogonal_spherical_average
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T18:51:48.295838+00:00
-- url     : https://prove2.me/submissions/6f024f2f-9010-41dd-affa-3bcdde18ca79

import Definitions.Def_FlatlyFoliatedRelativity_basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Support

open scoped Topology Pointwise
open FlatlyFoliated MeasureTheory Metric Set TopologicalSpace

noncomputable section

namespace OrthogonalAverage

set_option backward.isDefEq.respectTransparency false

private abbrev L := R3 →L[ℝ] R3
private abbrev G := unitary L
private abbrev K := {A : L // A ∈ closedBall 0 1}
private abbrev S := sphere (0 : R3) 1

private instance : ContinuousStar L := ⟨ContinuousLinearMap.adjoint.continuous⟩

private instance : CompactSpace G := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : L) 1).of_isClosed_subset isClosed_unitary
  intro A hA
  simp [mem_closedBall, dist_zero_right, CStarRing.norm_of_mem_unitary hA]

private instance : MeasurableSpace G := borel G
private instance : BorelSpace G := ⟨rfl⟩

private noncomputable def pc : PositiveCompacts G := ⟨⟨univ, isCompact_univ⟩, by simp⟩
private noncomputable def hm : Measure G := Measure.haarMeasure pc
private instance : IsProbabilityMeasure hm := ⟨by change Measure.haarMeasure pc (pc : Set G) = 1; exact Measure.haarMeasure_self⟩
private instance : hm.IsMulLeftInvariant := inferInstanceAs (Measure.haarMeasure pc).IsMulLeftInvariant
private instance : hm.IsOpenPosMeasure := inferInstanceAs (Measure.haarMeasure pc).IsOpenPosMeasure
private noncomputable def μ : Measure G := hm.inv
private instance : IsProbabilityMeasure μ := by
  constructor
  simp [μ, Measure.inv, Measure.map_apply measurable_inv MeasurableSet.univ]
private instance : μ.IsMulRightInvariant := inferInstanceAs hm.inv.IsMulRightInvariant
private instance : μ.IsOpenPosMeasure := inferInstanceAs hm.inv.IsOpenPosMeasure

private def embed (A : G) : K := ⟨A.1, by simp [mem_closedBall, CStarRing.norm_coe_unitary]⟩
private lemma cont_embed : Continuous embed := continuous_subtype_val.subtype_mk _

private def act (T : R3 ≃ₗᵢ[ℝ] R3) (u : S) : S :=
  ⟨T u.1, by simpa only [mem_sphere, dist_zero_right, T.norm_map] using u.2⟩

private lemma sphere_preserving (T : R3 ≃ₗᵢ[ℝ] R3) :
    MeasurePreserving (act T) (volume : Measure R3).toSphere (volume : Measure R3).toSphere := by
  have hc : Continuous (act T) := (T.continuous.comp continuous_subtype_val).subtype_mk _
  refine ⟨hc.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hc.measurable hs, Measure.toSphere_apply' _ (hc.measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have he : Ioo (0 : ℝ) 1 • (Subtype.val '' (act T ⁻¹' s)) =
      T ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨r, hr, T u.1, ⟨act T u, hu, rfl⟩, by simp⟩
    · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, hx⟩
      refine ⟨r, hr, T.symm u.1, ⟨act T.symm u, ?_, rfl⟩, ?_⟩
      · simpa [act] using hu
      · simpa using congrArg T.symm hx
  rw [he]
  exact T.measurePreserving.measure_preimage_emb T.toHomeomorph.measurableEmbedding _

private instance : NeZero (volume : Measure R3).toSphere := ⟨Measure.toSphere_ne_zero volume⟩

private noncomputable def σ : Measure S :=
  ((volume : Measure R3).toSphere univ)⁻¹ • (volume : Measure R3).toSphere
private instance : IsProbabilityMeasure σ := inferInstanceAs
  (IsProbabilityMeasure (((volume : Measure R3).toSphere univ)⁻¹ • (volume : Measure R3).toSphere))
private instance : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

private lemma c_int {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℝ} (hf : Continuous f) : Integrable f ν := by
  simpa using hf.continuousOn.integrableOn_compact (μ := ν) isCompact_univ

private lemma σ_preserving (T : R3 ≃ₗᵢ[ℝ] R3) : MeasurePreserving (act T) σ σ :=
  (sphere_preserving T).smul_measure _

private lemma sphere_integral (T : R3 ≃ₗᵢ[ℝ] R3) (g : R3 → ℝ) (r : ℝ) :
    (∫ u : S, g (T (r • u.1)) ∂σ) = ∫ u : S, g (r • u.1) ∂σ := by
  have he : MeasurableEmbedding (act T) :=
    ((T.continuous.comp continuous_subtype_val).subtype_mk _).isClosedEmbedding (by
      intro u v h
      exact Subtype.ext (T.injective (congrArg Subtype.val h))) |>.measurableEmbedding
  simpa [act] using (σ_preserving T).integral_comp he (fun u : S => g (r • u.1))

private lemma orbit_integral (g : R3 → ℝ) (x y : R3) (hxy : ‖x‖ = ‖y‖) :
    (∫ A : G, g (A.1 x) ∂μ) = ∫ A : G, g (A.1 y) ∂μ := by
  let T := (Submodule.span ℝ {y - x})ᗮ.reflection
  have ht : T y = x := Submodule.reflection_sub hxy.symm
  let B : G := Unitary.linearIsometryEquiv.symm T
  have hb : (B : L) y = x := ht
  have he : (fun A : G => g (A.1 x)) = (fun A : G => g ((A * B).1 y)) := by
    funext A
    change g (A.1 x) = g (A.1 (B.1 y))
    rw [hb]
  rw [he]
  exact integral_mul_right_eq_self (fun A : G => g (A.1 y)) B

private lemma average_formula (g : R3 → ℝ) (hg : Continuous g) (x : R3) :
    (∫ A : G, g (A.1 x) ∂μ) = sphSymmetrization g x := by
  have hc : Continuous (fun p : G × S => g (p.1.1 (‖x‖ • p.2.1))) := by
    apply hg.comp
    apply (continuous_subtype_val.comp continuous_fst).clm_apply
    exact (continuous_const : Continuous (fun _ : G × S => ‖x‖)).smul
      ((continuous_subtype_val : Continuous (Subtype.val : S → R3)).comp continuous_snd)
  have hi : Integrable (fun p : G × S => g (p.1.1 (‖x‖ • p.2.1))) (μ.prod σ) := c_int hc
  calc
    (∫ A : G, g (A.1 x) ∂μ) =
        ∫ u : S, ∫ A : G, g (A.1 (‖x‖ • u.1)) ∂μ ∂σ := by
      calc
        _ = ∫ _ : S, (∫ A : G, g (A.1 x) ∂μ) ∂σ := by simp
        _ = _ := integral_congr_ae (.of_forall fun u => orbit_integral g x _ (by
          have hu : ‖u.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using u.2
          simp [norm_smul, hu]))
    _ = ∫ A : G, ∫ u : S, g (A.1 (‖x‖ • u.1)) ∂σ ∂μ := (integral_integral_swap hi).symm
    _ = ∫ A : G, ∫ u : S, g (‖x‖ • u.1) ∂σ ∂μ := by
      apply integral_congr_ae
      exact .of_forall fun A => sphere_integral (Unitary.linearIsometryEquiv A) g ‖x‖
    _ = sphSymmetrization g x := by simp [sphSymmetrization, average, σ]

end OrthogonalAverage

open OrthogonalAverage in
theorem solution :
    ∃ ν : Measure {A : FlatlyFoliated.R3 →L[ℝ] FlatlyFoliated.R3 // A ∈ closedBall 0 1},
      IsProbabilityMeasure ν ∧
      (∀ᵐ A ∂ν, ∃ T : FlatlyFoliated.R3 ≃ₗᵢ[ℝ] FlatlyFoliated.R3,
        A.1 = T.toContinuousLinearEquiv.toContinuousLinearMap) ∧
      (⟨ContinuousLinearMap.id ℝ FlatlyFoliated.R3, by simp⟩ ∈ ν.support) ∧
      ∀ (g : FlatlyFoliated.R3 → ℝ), Continuous g → ∀ x,
        (∫ A, g (A.1 x) ∂ν) = FlatlyFoliated.sphSymmetrization g x := by
  let ν := μ.map embed
  have hn : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map cont_embed.aemeasurable
  refine ⟨ν, hn, ?_, ?_, ?_⟩
  · apply (ae_map_iff cont_embed.aemeasurable ?_).mpr
    · exact .of_forall fun A => ⟨Unitary.linearIsometryEquiv A, rfl⟩
    · have he : {A : K | ∃ T : R3 ≃ₗᵢ[ℝ] R3,
          A.1 = T.toContinuousLinearEquiv.toContinuousLinearMap} =
          Subtype.val ⁻¹' (unitary L : Set L) := by
        ext A
        constructor
        · rintro ⟨T, hT⟩
          change A.1 ∈ unitary L
          rw [hT]
          exact (Unitary.linearIsometryEquiv.symm T).2
        · intro hA
          exact ⟨Unitary.linearIsometryEquiv ⟨A.1, hA⟩, rfl⟩
      rw [he]
      exact (isClosed_unitary.preimage continuous_subtype_val).measurableSet
  · change embed (1 : G) ∈ (μ.map embed).support
    apply (Measure.mem_support_iff_forall _).mpr
    intro U hU
    have hp : embed ⁻¹' U ∈ nhds (1 : G) := cont_embed.continuousAt.preimage_mem_nhds hU
    exact (μ.measure_pos_of_mem_nhds hp).trans_le (Measure.le_map_apply cont_embed.aemeasurable U)
  · intro g hg x
    rw [show (∫ A, g (A.1 x) ∂ν) = ∫ A : G, g (A.1 x) ∂μ from
      integral_map cont_embed.aemeasurable (hg.comp (continuous_subtype_val.clm_apply continuous_const)).aestronglyMeasurable]
    exact average_formula g hg x
