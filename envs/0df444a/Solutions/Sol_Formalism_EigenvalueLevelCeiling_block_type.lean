-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.block_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:29:16.212613+00:00
-- url     : https://prove2.me/submissions/40594342-97d4-4048-a4d7-7bce10ed2f87

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : BlockType := by
  intro R _ I r t A A' B B' C C' D D' hM hB
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hM
  obtain ⟨hTL, hTR, -, -⟩ := hM
  have hB0 : B.map (Ideal.Quotient.mk I) = 0 := by
    ext i j
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hB i j)
  have hTL' : A.map (Ideal.Quotient.mk I) * A'.map (Ideal.Quotient.mk I) = 1 := by
    have h1 := congrArg (fun X => X.map (Ideal.Quotient.mk I)) hTL
    simp only [Matrix.map_add _ (map_add (Ideal.Quotient.mk I)), Matrix.map_mul, hB0, Matrix.zero_mul, add_zero,
      Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I))] at h1
    exact h1
  have hTR' : A.map (Ideal.Quotient.mk I) * B'.map (Ideal.Quotient.mk I) = 0 := by
    have h1 := congrArg (fun X => X.map (Ideal.Quotient.mk I)) hTR
    simp only [Matrix.map_add _ (map_add (Ideal.Quotient.mk I)), Matrix.map_mul, hB0, Matrix.zero_mul, add_zero,
      Matrix.map_zero _ (map_zero (Ideal.Quotient.mk I))] at h1
    exact h1
  have hA'A : A'.map (Ideal.Quotient.mk I) * A.map (Ideal.Quotient.mk I) = 1 := by
    first
      | exact mul_eq_one_comm.1 hTL'
      | exact Matrix.mul_eq_one_comm.mp hTL'
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hTL'
  have hB'0 : B'.map (Ideal.Quotient.mk I) = 0 := by
    calc B'.map (Ideal.Quotient.mk I)
        = (A'.map (Ideal.Quotient.mk I) * A.map (Ideal.Quotient.mk I)) * B'.map (Ideal.Quotient.mk I) := by
          rw [hA'A, Matrix.one_mul]
      _ = A'.map (Ideal.Quotient.mk I) * (A.map (Ideal.Quotient.mk I) * B'.map (Ideal.Quotient.mk I)) :=
          Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hTR', Matrix.mul_zero]
  have hent : ∀ {m n : Type} (X : Matrix m n R), X.map (Ideal.Quotient.mk I) = 0 → ∀ i j, X i j ∈ I := by
    intro m n X hX i j
    exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun hX i) j)
  refine ⟨?_, hent _ ?_, hent _ ?_, hent _ hB'0⟩
  · rw [← Ideal.Quotient.eq]
    simp only [RingHom.map_det, map_mul, RingHom.mapMatrix_apply, Matrix.fromBlocks_map, hB0,
      Matrix.det_fromBlocks_zero₁₂]
  · rw [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk I)), Matrix.map_mul,
      Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I)), hTL', sub_self]
  · rw [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk I)), Matrix.map_mul,
      Matrix.map_one _ (map_zero (Ideal.Quotient.mk I)) (map_one (Ideal.Quotient.mk I)), hA'A, sub_self]
end Formalism.EigenvalueLevelCeiling
