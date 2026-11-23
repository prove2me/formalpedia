-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.dualMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:58.884577+00:00
-- url     : https://prove2.me/submissions/7326ec47-90cf-490b-9df8-190eba3c2c04

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_charOf_eq_iff
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
variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution {A : AddSubgroup K} (hA : perp ψ A = A) {L : AddSubgroup K} {z : K}
    (hz : z ∈ perp ψ L) :
    dualMap ψ A L ((⟨z, hz⟩ : perp ψ L) : perp ψ L ⧸ A.addSubgroupOf (perp ψ L)) = charOf A hz := by
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add (A.addSubgroupOf (perp ψ L)) (⟨z, hz⟩ : perp ψ L)
  rw [dualMap, charOf_eq_iff, hA, hl]
  have : ((l : perp ψ L) : K) ∈ A := AddSubgroup.mem_addSubgroupOf.1 l.2
  simpa using this
end Formalism.FourierDecayAlt.P.A6x3
