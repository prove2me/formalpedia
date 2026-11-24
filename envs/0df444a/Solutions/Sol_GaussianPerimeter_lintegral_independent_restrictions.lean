-- Prove2me | solution 1 for GaussianPerimeter.lintegral_independent_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:10:39.065215+00:00
-- url     : https://prove2.me/submissions/4216e66a-8fb1-4f51-bf13-f98063ba862a

module
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_GaussianPerimeter_Sphere

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Function
open scoped ENNReal Pointwise RealInnerProductSpace
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B)
    [SFinite ν] {N : ℕ} (i : Fin (N + 1)) (weight : A → B → ℝ≥0∞)
    (accept : A → B → A → Prop)
    (hw : Measurable (uncurry weight))
    (ha : MeasurableSet {q : (A × B) × A | accept q.1.1 q.1.2 q.2}) :
    (∫⁻ u, ∫⁻ y, {u | ∀ j ≠ i, accept (u i) y (u j)}.indicator
      (fun u => weight (u i) y) u ∂ν ∂Measure.pi (fun _ : Fin (N + 1) => μ)) =
    ∫⁻ a, ∫⁻ y, μ {v | accept a y v} ^ N * weight a y ∂ν ∂μ := by
  classical
  let μN : Measure (Fin N → A) := Measure.pi fun _ => μ
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => A) i).symm
  have hpres : MeasurePreserving e (μ.prod μN) (Measure.pi (fun _ => μ)) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) i).symm
  let ok (a : A) (y : B) : Set (Fin N → A) := univ.pi fun _ => {v | accept a y v}
  let f (a : A) (z : Fin N → A) (y : B) := (ok a y).indicator (fun _ => weight a y) z
  have hrepr (z : A × (Fin N → A)) (y : B) :
      {u | ∀ j ≠ i, accept (u i) y (u j)}.indicator
        (fun u => weight (u i) y) (e z) = f z.1 z.2 y := by
    let u : Fin (N + 1) → A := @Fin.insertNth N (fun _ => A) i z.1 z.2
    change {u' | ∀ j ≠ i, accept (u' i) y (u' j)}.indicator (fun u' => weight (u' i) y) u = _
    have heq : (∀ j ≠ i, accept z.1 y (@Fin.insertNth N (fun _ => A) i z.1 z.2 j)) ↔ z.2 ∈ ok z.1 y := by
      simp only [ok, mem_univ_pi, mem_ofPred_eq]
      constructor
      · intro h j
        simpa only [Fin.insertNth_apply_succAbove] using h (i.succAbove j) (i.succAbove_ne j)
      · intro h j hj
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        simpa only [Fin.insertNth_apply_succAbove] using h k
    have hui : u i = z.1 := Fin.insertNth_apply_same _ _ _
    simp only [indicator, mem_ofPred_eq, hui, f]
    simp only [show (∀ j ≠ i, accept z.1 y (u j)) ↔ z.2 ∈ ok z.1 y from heq]
  have h_joint : Measurable (fun z : (A × (Fin N → A)) × B => f z.1.1 z.1.2 z.2) := by
    apply Measurable.indicator
    · exact hw.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · suffices hs : {z : (A × (Fin N → A)) × B | z.1.2 ∈ ok z.1.1 z.2} =
          ⋂ j : Fin N, (fun z : (A × (Fin N → A)) × B => ((z.1.1, z.2), z.1.2 j)) ⁻¹'
            {q : (A × B) × A | accept q.1.1 q.1.2 q.2} by
        change MeasurableSet {z : (A × (Fin N → A)) × B | z.1.2 ∈ ok z.1.1 z.2}
        rw [hs]
        apply MeasurableSet.iInter
        intro j
        exact ha.preimage (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
          ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)))
      ext z
      simp [ok]
  have h_joint' (a : A) : Measurable (uncurry (f a)) := by
    exact h_joint.comp (((measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  calc
    _ = ∫⁻ z : A × (Fin N → A), ∫⁻ y, f z.1 z.2 y ∂ν ∂(μ.prod μN) := by
      rw [← hpres.lintegral_comp_emb e.measurableEmbedding]
      simp only [hrepr]
    _ = ∫⁻ a, ∫⁻ z, ∫⁻ y, f a z y ∂ν ∂μN ∂μ :=
      lintegral_prod _ (h_joint.lintegral_prod_right').aemeasurable
    _ = ∫⁻ a, ∫⁻ y, ∫⁻ z, f a z y ∂μN ∂ν ∂μ := by
      apply lintegral_congr
      intro a
      exact lintegral_lintegral_swap (h_joint' a).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro y
      have hpart : MeasurableSet {v | accept a y v} :=
        ha.preimage (show Measurable (fun v : A => ((a, y), v)) from
          measurable_const.prodMk measurable_id)
      change (∫⁻ z, (ok a y).indicator (fun _ => weight a y) z ∂μN) = _
      rw [lintegral_indicator_const (MeasurableSet.univ_pi fun _ => hpart), mul_comm]
      simp [μN, Measure.pi_pi]
end GaussianPerimeter
