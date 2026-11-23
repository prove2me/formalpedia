-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shf_vecMul_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:06.057186+00:00
-- url     : https://prove2.me/submissions/b3d40af5-132b-4501-b6bf-1065a6ddff5e

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {p : Matrix (Fin n) (Fin n) K} (hp : IsP R k p) (β : Fin n → K)
    (hβi : ∀ b, β b ∈ R) (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) : ∀ b, (β ᵥ* p) b ∈ R := by
  intro b
  simp only [Matrix.vecMul, dotProduct]
  refine R.sum_mem fun a _ => ?_
  by_cases h : k < a.val
  · exact R.mul_mem (hβi a) (hp.2 a b (Or.inl h))
  · rw [hβ a (by omega), zero_mul]; exact R.zero_mem
end Formalism.FourierDecayAlt.P.A5x9
