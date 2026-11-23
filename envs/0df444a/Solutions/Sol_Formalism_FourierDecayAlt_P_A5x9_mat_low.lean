-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.mat_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:17.088986+00:00
-- url     : https://prove2.me/submissions/895b158a-937d-40a9-b761-e3ac3d958f75

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
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
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {q : Matrix (Fin n) (Fin n) K} (hq : IsP R k q) (t : Fin n → R)
    (ht : ∀ j : Fin n, k < j.val → t j = 0) :
    ∃ s : Fin n → R, (∀ j : Fin n, k < j.val → s j = 0) ∧ coeLin R s = q *ᵥ coeLin R t := by
  have hmem : ∀ a, (q *ᵥ coeLin R t) a ∈ R := by
    intro a
    simp only [Matrix.mulVec, dotProduct]
    refine R.sum_mem fun b _ => ?_
    rw [coeLin_apply]
    by_cases hb : b.val ≤ k
    · exact R.mul_mem (hq.2 a b (Or.inr hb)) (t b).2
    · rw [ht b (by omega)]; simp [R.zero_mem]
  refine ⟨fun a => ⟨_, hmem a⟩, fun j hj => ?_, ?_⟩
  · apply Subtype.ext
    show (q *ᵥ coeLin R t) j = 0
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [coeLin_apply]
    by_cases hb : b.val ≤ k
    · rw [up_zero hq.1 (show b < j from Fin.lt_def.2 (by omega)), zero_mul]
    · rw [ht b (by omega)]; simp
  · funext a
    rw [coeLin_apply]
end Formalism.FourierDecayAlt.P.A5x9
