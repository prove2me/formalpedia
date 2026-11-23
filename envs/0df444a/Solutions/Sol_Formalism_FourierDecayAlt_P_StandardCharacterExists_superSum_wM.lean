-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.superSum_wM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:17.554714+00:00
-- url     : https://prove2.me/submissions/8ffe929d-86cf-4739-a71f-a4b4070c2090

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wM_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wM_zero_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_ex_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P.StandardCharacterExists
theorem _root_.solution (m : ℕ) (X : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) (B ρ : Fin (m + 2) → ℂ) (σ : ℂ) :
    superSum (wMat (m + 3) * Mcoord 0 X B ρ σ) =
      ρ 1 + ∑ k ∈ Finset.Ico 0 (m + 1), ex (blk X B 0 0) k (k + 2) := by
  unfold superSum
  rw [Fin.sum_univ_succ]
  congr 1
  · have := wM_zero_cast X B ρ σ 1
    simpa using this
  · rw [← Finset.range_eq_Ico, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.succ_castSucc, wM_succ]
    simpa using (ex_fin (blk X B 0 0) i.castSucc.castSucc i.succ.succ).symm
end Formalism.FourierDecayAlt.P.StandardCharacterExists
