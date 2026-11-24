-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.io_comm_vlet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:56.98295+00:00
-- url     : https://prove2.me/submissions/346917f1-3cdf-47b4-bbde-b0a4d0393af5

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_comm_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_comm_Ts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_comm_Ts_star

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
theorem _root_.solution (σ : Site A) (x : A) (h : ∀ y ∈ ops σ, Commute y x) (l : Letter K S) :
    Commute (io x) (vlet σ l : SlopeTestRemainingChoices S A) := by
  unfold vlet
  apply io_comm_ins
  intro i j
  have hφ : ∀ (k : K) (r : A), Commute ((RingHom.id A) (algebraMap K A k)) r :=
    fun k r => Algebra.commutes k r
  by_cases hl : l.plus = true
  · rw [if_pos hl]
    exact (comm_Ts (RingHom.id A) hφ σ x h l.pt i j).symm
  · rw [if_neg hl]
    exact (comm_Ts_star (RingHom.id A) hφ σ x h l.pt i j).symm
end Formalism.FourierDecayAlt.P.Wd8
