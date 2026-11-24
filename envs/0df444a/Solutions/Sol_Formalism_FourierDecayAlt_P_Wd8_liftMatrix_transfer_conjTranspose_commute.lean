-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.liftMatrix_transfer_conjTranspose_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:39.75566+00:00
-- url     : https://prove2.me/submissions/47bff253-df59-48fd-868b-592ea3d257dc

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_liftMatrix_commute_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_algebraMap_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_comm_Ts_star
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
theorem _root_.solution {τ : Site A} {b : SlopeTestRemainingChoices S A} (h : CC τ b) (Y : K) :
    Commute (lift0 (Ts τ Y)ᴴ) (d0 b) := by
  have hφ : ∀ (k : K) (r : SlopeTestRemainingChoices S A),
      Commute ((Matrix.scalar (Ix S) : A →+* SlopeTestRemainingChoices S A) (algebraMap K A k)) r :=
    fun k r => io_algebraMap_comm k r
  have h' : ∀ x ∈ ops τ, Commute ((Matrix.scalar (Ix S) : A →+* SlopeTestRemainingChoices S A) x) b := h
  exact liftMatrix_commute_diagScalar _ _ fun i j => comm_Ts_star _ hφ τ b h' Y j i
end Formalism.FourierDecayAlt.P.Wd8
