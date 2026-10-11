-- Prove2me | solution 1 for DRConvexOpt.Lifting.theorem_5_i
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:02:59.993675+00:00
-- url     : https://prove2.me/submissions/0e46a3a1-e37a-400b-8ecc-03cba13f03b7

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

namespace RRAux_DRConvexOpt_Lifting_theorem_5_i

open MeasureTheory

theorem convex_of_cone {m : ℕ} {K : Set (Fin m → ℝ)} (hK : DRConvexOpt.Reform.IsProperCone K) :
    Convex ℝ K := by
  obtain ⟨_, _, hadd, hsmul, _, _⟩ := hK
  intro x hx y hy a b ha hb _
  exact hadd _ (hsmul x hx a ha) _ (hsmul y hy b hb)

end RRAux_DRConvexOpt_Lifting_theorem_5_i

open MeasureTheory in
open DRConvexOpt.Lifting in
-- Theorem 5 (i) (Lifting Theorem), p. 15.
theorem solution {nP nM nI : ℕ} (g : (Fin nP → ℝ) → (Fin nM → ℝ)) (hg : Measurable g)
    (f : Fin nM → ℝ) (K : Set (Fin nM → ℝ)) (hK : DRConvexOpt.Reform.IsProperCone K)
    (C : Fin nI → Set (Fin nP → ℝ)) (hC : ∀ i, MeasurableSet (C i)) (plo phi : Fin nI → ℝ) :
    momentSet g f K C plo phi = marginal (liftedSet g f K C plo phi) := by
  have hKc : IsClosed K := hK.1
  have hKm : MeasurableSet K := hKc.measurableSet
  have hKconv := RRAux_DRConvexOpt_Lifting_theorem_5_i.convex_of_cone hK
  have hSm : MeasurableSet {ω : (Fin nP → ℝ) × (Fin nM → ℝ) | ω.2 - g ω.1 ∈ K} :=
    (measurable_snd.sub (hg.comp measurable_fst)) hKm
  ext ν
  constructor
  · rintro ⟨hprob, hint, hcK, hCi⟩
    set c := f - ∫ z, g z ∂ν with hc
    let φ : (Fin nP → ℝ) → (Fin nP → ℝ) × (Fin nM → ℝ) := fun z => (z, g z + c)
    have hφ : Measurable φ := measurable_id.prodMk (hg.add measurable_const)
    refine ⟨ν.map φ, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact Measure.isProbabilityMeasure_map hφ.aemeasurable
    · rw [integrable_map_measure measurable_snd.aestronglyMeasurable hφ.aemeasurable]
      exact hint.add (integrable_const c)
    · exact (integrable_map_measure (g := fun ω : (Fin nP → ℝ) × (Fin nM → ℝ) => g ω.1)
        (hg.comp measurable_fst).aestronglyMeasurable hφ.aemeasurable).2 hint
    · rw [integral_map hφ.aemeasurable measurable_snd.aestronglyMeasurable]
      show ∫ x, (g x + c) ∂ν = f
      rw [integral_add hint (integrable_const c), integral_const]
      simp [hc]
    · rw [Measure.map_apply hφ hSm]
      have : φ ⁻¹' {ω | ω.2 - g ω.1 ∈ K} = Set.univ := by
        ext z; simp [φ, hcK]
      rw [this, measure_univ]
    · intro i
      rw [measureReal_def, Measure.map_apply hφ (measurable_fst (hC i))]
      have : φ ⁻¹' (Prod.fst ⁻¹' C i) = C i := rfl
      rw [this, ← measureReal_def]
      exact hCi i
    · show (ν.map φ).map Prod.fst = ν
      rw [Measure.map_map measurable_fst hφ]
      have : Prod.fst ∘ φ = id := rfl
      rw [this, Measure.map_id]
  · rintro ⟨μ, ⟨hprob, hint2, hintg, hf, hS, hCi⟩, rfl⟩
    refine ⟨Measure.isProbabilityMeasure_map measurable_fst.aemeasurable, ?_, ?_, ?_⟩
    · rw [integrable_map_measure hg.aestronglyMeasurable measurable_fst.aemeasurable]
      exact hintg
    · rw [integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable, ← hf,
        ← integral_sub hint2 hintg]
      refine hKconv.integral_mem hKc ?_ (hint2.sub hintg)
      have h0 : μ {ω : (Fin nP → ℝ) × (Fin nM → ℝ) | ω.2 - g ω.1 ∈ K}ᶜ = 0 :=
        (prob_compl_eq_zero_iff hSm).2 hS
      exact mem_ae_iff.2 h0
    · intro i
      rw [measureReal_def, Measure.map_apply measurable_fst (hC i), ← measureReal_def]
      exact hCi i

#print axioms solution
