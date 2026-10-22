-- Prove2me | solution 1 for DRConvexOpt.Lifting.marginal_subset_momentSet
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:05:34.592979+00:00
-- url     : https://prove2.me/submissions/d7110cd5-4198-471b-838e-d83d0716b41f

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

set_option autoImplicit false
open MeasureTheory DRConvexOpt.Lifting

theorem solution {nP nM nI : ℕ} (g : (Fin nP → ℝ) → (Fin nM → ℝ))
    (hg : Measurable g) (f : Fin nM → ℝ) (K : Set (Fin nM → ℝ)) (hK : DRConvexOpt.Reform.IsProperCone K)
    (C : Fin nI → Set (Fin nP → ℝ)) (hC : ∀ i, MeasurableSet (C i)) (plo phi : Fin nI → ℝ) :
    marginal (liftedSet g f K C plo phi) ⊆ momentSet g f K C plo phi := by
  rintro ν ⟨μ, ⟨hprob, hint2, hintg, hmean, hcone, hC'⟩, rfl⟩
  have : IsProbabilityMeasure μ := hprob
  obtain ⟨hcl, h0, hadd, hsmul, -, -⟩ := hK
  have hconv : Convex ℝ K := by
    intro x hx y hy a b ha hb _
    exact hadd _ (hsmul x hx a ha) _ (hsmul y hy b hb)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  · exact (integrable_map_measure hg.aestronglyMeasurable measurable_fst.aemeasurable).2 hintg
  · rw [integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
    have hSm : MeasurableSet {ω : (Fin nP → ℝ) × (Fin nM → ℝ) | ω.2 - g ω.1 ∈ K} :=
      hcl.measurableSet.preimage (measurable_snd.sub (hg.comp measurable_fst))
    have hae : ∀ᵐ ω ∂μ, ω.2 - g ω.1 ∈ K := by
      have := (prob_compl_eq_zero_iff hSm).mpr hcone
      exact this
    have hmem := hconv.integral_mem hcl hae (hint2.sub hintg)
    rw [integral_sub hint2 hintg, hmean] at hmem
    exact hmem
  · intro i
    have := hC' i
    have e : ((μ.map Prod.fst).real (C i)) = μ.real (Prod.fst ⁻¹' C i) := by
      simp [Measure.real, Measure.map_apply measurable_fst (hC i)]
    rw [e]; exact this
