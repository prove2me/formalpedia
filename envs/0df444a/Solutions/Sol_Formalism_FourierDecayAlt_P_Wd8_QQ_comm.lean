-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.QQ_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:40.560798+00:00
-- url     : https://prove2.me/submissions/d8b2641f-6e61-4e88-bf2a-a922c07ed54a

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_liftMatrix_commute_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_comm_bT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_liftMatrix_commute_diagScalar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (QQ : K → M2 A) (sites : List (Site A)) (w : List (Letter K S)) (Y : K)
    (h : ∀ σ ∈ sites, QQCommutes QQ σ) :
    Commute (lift0 (QQ Y)) (d0 (sites.map fun σ => bT σ w).prod) := by
  refine liftMatrix_commute_diagScalar _ _ fun i j => Commute.list_prod_right _ _ fun b hb => ?_
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hb
  exact io_comm_bT σ _ (fun y hy => (h σ hσ Y i j y hy).symm) w
end Formalism.FourierDecayAlt.P.Wd8
