-- Prove2me | solution 1 for BookProof.ChapterCyclicDirectSum.starProjection_eq_of_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:17:52.864529+00:00
-- url     : https://prove2.me/submissions/a922fa58-f37e-4a91-b821-3999f083b6e3

-- Generated from ChapterCyclicDirectSum.lean — solution of BookProof.ChapterCyclicDirectSum.starProjection_eq_of_hasSum
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDirectSum



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterCyclicDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} {V : ι → Submodule ℂ H}
    [∀ i, (V i).HasOrthogonalProjection]
    (hV : OrthogonalFamily ℂ (fun i => (V i)) fun i => (V i).subtypeₗᵢ)
    {c : ι → H} (hc : ∀ i, c i ∈ V i) {v : H} (h : HasSum c v) (j : ι) :
    (V j).starProjection v = c j := by

  classical
  have hstep : ∀ i, (V j).starProjection (c i) = if i = j then c j else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [Submodule.starProjection_eq_self_iff.2 (hc i)]
    · have hzero : (V j).starProjection (c i) = 0 := by
        have hmem : c i ∈ (V j)ᗮ :=
          Submodule.isOrtho_iff_le.1 (hV.isOrtho hij) (hc i)
        exact Submodule.eq_starProjection_of_mem_orthogonal' (V j).zero_mem hmem (by simp)
      simp [hij, hzero]
  have h1 : HasSum (fun i => (V j).starProjection (c i)) ((V j).starProjection v) :=
    (V j).starProjection.hasSum h
  have h2 : HasSum (fun i => (V j).starProjection (c i)) (c j) := by
    simpa only [hstep] using hasSum_ite_eq j (c j)
  exact h1.unique h2
