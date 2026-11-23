-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.out_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:20.410144+00:00
-- url     : https://prove2.me/submissions/0cdaab57-492c-47e8-824c-880509f0a219

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution {Λ' Λ : AddSubgroup K} (h : Λ' ≤ Λ) (y : K ⧸ Λ') :
    (Quotient.out (AddSubgroup.quotientEquivProdOfLE h y).1 : K) - (Quotient.out y : K) ∈ Λ := by
  have h1 : (AddSubgroup.quotientEquivProdOfLE h y).1 = ((Quotient.out y : K) : K ⧸ Λ) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' y]
    rfl
  rw [h1]
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add Λ (Quotient.out y : K)
  rw [hl]
  simp
end Formalism.FourierDecayAlt.P.A6x3
