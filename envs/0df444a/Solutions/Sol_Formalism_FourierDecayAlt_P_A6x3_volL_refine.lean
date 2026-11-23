-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.volL_refine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:43.222127+00:00
-- url     : https://prove2.me/submissions/50c77fa7-add3-4f85-87a2-06fbc33ec7ac

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_eq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution {R : Subring K} (hR : Lat R.toAddSubgroup) {Λ' Λ : AddSubgroup K}
    (hΛ' : Lat Λ') (hΛ : Lat Λ) (h : Λ' ≤ Λ) :
    volL R Λ = (Λ'.relIndex Λ : ℝ) * volL R Λ' := by
  rw [volL_eq, volL_eq, ← gi_trans hΛ hΛ' hR]
  congr 1
  rw [gi, AddSubgroup.relIndex_eq_one.2 h]
  simp
end Formalism.FourierDecayAlt.P.A6x3
