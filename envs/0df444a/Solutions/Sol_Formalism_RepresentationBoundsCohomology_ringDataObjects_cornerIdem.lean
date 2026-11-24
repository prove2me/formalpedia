-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.cornerIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:21.467808+00:00
-- url     : https://prove2.me/submissions/fd44b192-2d65-4d82-aa43-e05125c77188

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution : CornerIdempotentInSubalgebra := by
  unfold CornerIdempotentInSubalgebra
  intro k _ n ι _ _ B hn hsurj A
  classical
  obtain ⟨p, q, hpq⟩ : ∃ p q : n, p ≠ q := Fintype.exists_pair_of_one_lt_card hn
  have hc : ((Matrix.single p p (1 : k) - Matrix.single q q 1 : Matrix n n k), (0 : ι → k)) ∈ B := by
    obtain ⟨z1, hz1B, hz1⟩ := hsurj (Matrix.single p q 1)
    obtain ⟨z2, hz2B, hz2⟩ := hsurj (Matrix.single q p 1)
    have := B.sub_mem (B.mul_mem hz1B hz2B) (B.mul_mem hz2B hz1B)
    convert this using 1
    refine Prod.ext ?_ ?_
    · simp [hz1, hz2, Matrix.single_mul_single_same]
    · simp [mul_comm]
  have hij : ∀ i j, ((Matrix.single i j (1 : k) : Matrix n n k), (0 : ι → k)) ∈ B := by
    intro i j
    obtain ⟨w1, hw1B, hw1⟩ := hsurj (Matrix.single i p 1)
    obtain ⟨w2, hw2B, hw2⟩ := hsurj (Matrix.single p j 1)
    have := B.mul_mem (B.mul_mem hw1B hc) hw2B
    convert this using 1
    refine Prod.ext ?_ ?_
    · simp [hw1, hw2, Matrix.mul_sub, Matrix.sub_mul, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne, hpq]
    · simp
  have hA : (A, (0 : ι → k)) = ∑ i, ∑ j, A i j • ((Matrix.single i j (1 : k) : Matrix n n k), (0 : ι → k)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum, Prod.smul_fst, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single A
    · simp [Prod.snd_sum]
  rw [hA]
  exact B.sum_mem fun i _ => B.sum_mem fun j _ => B.smul_mem (hij i j) _
end Formalism.RepresentationBoundsCohomology.ringDataObjects
