-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.prod_Ioc_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:16:06.070552+00:00
-- url     : https://prove2.me/submissions/e83cf2eb-d1cc-4bb9-a99e-197625dbe476

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (f : ℕ → ℝ) (p a b : ℕ) :
    ∏ j ∈ Ioc (a + p) (b + p), f j = ∏ j ∈ Ioc a b, f (j + p) := by
  first
  | (rw [← Finset.map_add_right_Ioc, Finset.prod_map]; rfl)
  | (rw [← Finset.map_add_right_Ioc, Finset.prod_map]; simp [addRightEmbedding])
  | (apply Finset.prod_nbij' (fun j => j - p) (fun j => j + p) <;> intro j hj <;>
      simp only [Finset.mem_Ioc] at hj ⊢ <;> first | omega | (congr 1; omega))
end Formalism.FourierDecayAlt.P.Sz5
