-- Prove2me | solution 1 for BookProof.ChapterFreeFieldSphereSupport.stdGaussian_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:40:15.062526+00:00
-- url     : https://prove2.me/submissions/3fadeb5b-0ca7-4f32-97af-9bb4dec29b65

import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Mathlib
import Definitions.Def_ChapterFreeFieldSphereSupport

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport in
theorem solution {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    stdGaussian n {x} = 0 := by
  unfold BookProof.ChapterFreeFieldGaussian.stdGaussian
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpre : (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' {x}
      = Set.univ.pi (fun i => ({x.ofLp i} : Set ℝ)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ_pi]
    constructor
    · rintro rfl i; rfl
    · intro h
      ext i
      exact h i
  rw [hpre, Measure.pi_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ ⟨0, hn⟩)
  exact gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton)
