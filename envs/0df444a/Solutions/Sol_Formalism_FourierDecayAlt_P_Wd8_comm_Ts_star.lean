-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.comm_Ts_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:44.850404+00:00
-- url     : https://prove2.me/submissions/c1b509d5-05bc-4019-a499-c8dc9fbf4958

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mem_ops_sp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mem_ops_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mem_ops_sci

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
theorem _root_.solution {R : Type} [Ring R] (φ : A →+* R)
    (hφ : ∀ (k : K) (r : R), Commute (φ (algebraMap K A k)) r)
    (τ : Site A) (b : R) (h : ∀ x ∈ ops τ, Commute (φ x) b) (Y : K) (i j : Fin 2) :
    Commute (φ (star (Ts τ Y i j))) b := by
  have hp := h _ (mem_ops_sp τ)
  have hc := h _ (mem_ops_sc τ)
  have hci := h _ (mem_ops_sci τ)
  have hY : Commute (φ (star (algebraMap K A Y))) b := by
    rw [← algebraMap_star_comm]
    exact hφ _ b
  fin_cases i <;> fin_cases j <;> simp [Ts, Tm, hc, hci] <;>
    first | exact hY.add_left hp | exact (hφ (star Y) b).add_left hp
end Formalism.FourierDecayAlt.P.Wd8
