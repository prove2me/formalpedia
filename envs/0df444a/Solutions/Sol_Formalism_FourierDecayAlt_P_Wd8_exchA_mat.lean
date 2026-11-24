-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.exchA_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:48.010167+00:00
-- url     : https://prove2.me/submissions/90746c96-4800-4999-93c3-a2ce3bd90811

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exch_list
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_liftMatrix_list_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_diagScalar_list_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_cc_bT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_sitesCommute_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_liftMatrix_transfer_commute_diagScalar

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
theorem _root_.solution (sites : List (Site A)) (w : List (Letter K S)) (Y : K)
    (h1 : ∀ σ ∈ sites, Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w) = d0 (bT σ w) * lift0 (Ts σ Y) * Xp w Y)
    (h2 : sites.Pairwise SitesCommute) :
    Xp w Y * lift0 (sites.map fun σ => Ts σ Y).prod * d0 (sites.map fun σ => bT σ w).prod =
      d0 (sites.map fun σ => bT σ w).prod * lift0 (sites.map fun σ => Ts σ Y).prod * Xp w Y := by
  have e := exch_list (Xp w Y) (fun σ => lift0 (Ts σ Y)) (fun σ => d0 (bT σ w)) sites h1
    (h2.imp fun {σ τ} hst =>
      ⟨liftMatrix_transfer_commute_diagScalar (cc_bT hst w) Y, liftMatrix_transfer_commute_diagScalar (cc_bT (sitesCommute_symm hst) w) Y⟩)
  rw [liftMatrix_list_prod, diagScalar_list_prod, List.map_map, List.map_map]
  exact e
end Formalism.FourierDecayAlt.P.Wd8
