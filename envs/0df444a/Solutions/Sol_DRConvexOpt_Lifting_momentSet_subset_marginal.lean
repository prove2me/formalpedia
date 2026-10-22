-- Prove2me | solution 1 for DRConvexOpt.Lifting.momentSet_subset_marginal
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:04:58.118491+00:00
-- url     : https://prove2.me/submissions/fcc61c76-4d44-4067-8d50-0deb2162363b

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

set_option autoImplicit false
open MeasureTheory DRConvexOpt.Lifting

theorem solution {nP nM nI : ℕ} (g : (Fin nP → ℝ) → (Fin nM → ℝ))
    (hg : Measurable g) (f : Fin nM → ℝ) (K : Set (Fin nM → ℝ)) (hK : DRConvexOpt.Reform.IsProperCone K)
    (C : Fin nI → Set (Fin nP → ℝ)) (hC : ∀ i, MeasurableSet (C i)) (plo phi : Fin nI → ℝ)
    (ν : Measure (Fin nP → ℝ)) (hν : ν ∈ momentSet g f K C plo phi) :
    ν.map (fun z => (z, g z - ∫ z', g z' ∂ν + f)) ∈ liftedSet g f K C plo phi ∧
      (ν.map (fun z => (z, g z - ∫ z', g z' ∂ν + f))).map Prod.fst = ν := by
  obtain ⟨hprob, hint, hKmem, hC'⟩ := hν
  obtain ⟨hcl, h0, hadd, hsmul, -, -⟩ := hK
  have : IsProbabilityMeasure ν := hprob
  have hF : Measurable (fun z : Fin nP → ℝ => (z, g z - ∫ z', g z' ∂ν + f)) :=
    measurable_id.prodMk ((hg.sub measurable_const).add measurable_const)
  have hfst : (ν.map (fun z : Fin nP → ℝ => (z, g z - ∫ z', g z' ∂ν + f))).map Prod.fst = ν := by
    rw [Measure.map_map measurable_fst hF]
    exact Measure.map_id
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hfst⟩
  · exact Measure.isProbabilityMeasure_map hF.aemeasurable
  · rw [integrable_map_measure measurable_snd.aestronglyMeasurable hF.aemeasurable]
    exact (hint.sub (integrable_const _)).add (integrable_const _)
  · exact (integrable_map_measure (hg.comp measurable_fst).aestronglyMeasurable hF.aemeasurable).2 hint
  · rw [integral_map hF.aemeasurable measurable_snd.aestronglyMeasurable]
    show ∫ z, (g z - ∫ z', g z' ∂ν + f) ∂ν = f
    have h1 : Integrable (fun z => g z - ∫ z', g z' ∂ν) ν := hint.sub (integrable_const _)
    rw [integral_add h1 (integrable_const f), integral_sub hint (integrable_const _)]
    simp
  · have hSm : MeasurableSet {ω : (Fin nP → ℝ) × (Fin nM → ℝ) | ω.2 - g ω.1 ∈ K} :=
      hcl.measurableSet.preimage (measurable_snd.sub (hg.comp measurable_fst))
    rw [Measure.map_apply hF hSm]
    have : (fun z : Fin nP → ℝ => (z, g z - ∫ z', g z' ∂ν + f)) ⁻¹'
        {ω : (Fin nP → ℝ) × (Fin nM → ℝ) | ω.2 - g ω.1 ∈ K} = Set.univ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have : g z - ∫ z', g z' ∂ν + f - g z = f - ∫ z', g z' ∂ν := by abel
      rw [this]; exact hKmem
    rw [this]; exact measure_univ
  · intro i
    have e : ((ν.map (fun z : Fin nP → ℝ => (z, g z - ∫ z', g z' ∂ν + f))).real (Prod.fst ⁻¹' C i))
        = ν.real (C i) := by
      simp [Measure.real, Measure.map_apply hF (measurable_fst (hC i))]
      rfl
    rw [e]; exact hC' i
