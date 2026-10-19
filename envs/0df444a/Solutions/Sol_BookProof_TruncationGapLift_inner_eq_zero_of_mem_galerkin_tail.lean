-- Prove2me | solution 1 for BookProof.TruncationGapLift.inner_eq_zero_of_mem_galerkin_tail
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T13:10:48.394144+00:00
-- url     : https://prove2.me/submissions/b2d26ff1-0434-4195-99ad-78cea8ce1385

-- Generated from ChapterTruncationGapLift.lean — solution of BookProof.TruncationGapLift.inner_eq_zero_of_mem_galerkin_tail
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.TruncationGapLift



noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) {m : ℕ}
    {x w : F} (hx : x ∈ galerkinSpan b m) (hw : w ∈ tailSpan b m) :
    (inner ℂ x w : ℂ) = 0 := by

  have hgen : ∀ j : ℕ, m ≤ j → ∀ y ∈ galerkinSpan b m, (inner ℂ y (b j) : ℂ) = 0 := by
    intro j hj y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, hi, rfl⟩ := hz
        simp only [Set.mem_setOf_eq] at hi
        exact b.orthonormal.2 (by omega)
    | zero => simp
    | add u v _ _ hu hv => rw [inner_add_left, hu, hv, add_zero]
    | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]
  induction hw using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨j, hj, rfl⟩ := hz
      exact hgen j hj x hx
  | zero => simp
  | add u v _ _ hu hv => rw [inner_add_right, hu, hv, add_zero]
  | smul c u _ hu => rw [inner_smul_right, hu, mul_zero]
