-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.comm_Ts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:44.385989+00:00
-- url     : https://prove2.me/submissions/6ee3f5d9-0ece-4999-b184-4c79d9c2e525

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mem_ops_p
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mem_ops_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mem_ops_ci

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
theorem _root_.solution {R : Type} [Ring R] (φ : A →+* R) (hφ : ∀ (k : K) (r : R), Commute (φ (algebraMap K A k)) r)
    (τ : Site A) (b : R) (h : ∀ x ∈ ops τ, Commute (φ x) b) (Y : K) (i j : Fin 2) :
    Commute (φ (Ts τ Y i j)) b := by
  have hp := h _ (mem_ops_p τ)
  have hc := h _ (mem_ops_c τ)
  have hci := h _ (mem_ops_ci τ)
  have hY := hφ Y b
  fin_cases i <;> fin_cases j <;> simp [Ts, Tm, hc, hci] <;> exact hY.add_left hp
end Formalism.FourierDecayAlt.P.Wd8
