-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.fm_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:15.964795+00:00
-- url     : https://prove2.me/submissions/99eb6909-0b0a-4b2c-8dd4-84a69e595063

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_cj_back
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_mem_lowW_scale_iff
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution : Function.Surjective (fm S T c) := by
  rintro ⟨⟨v, hv⟩, ⟨u, hu⟩⟩
  refine ⟨(⟨v, (mem_lowW_scale_iff S T c).1 hv⟩, ⟨DG (dg S c) * u * (DG (dg S c))⁻¹, ?_⟩), ?_⟩
  · have : IsUpUni ((cj (dg S c) (DG (dg S c) * u * (DG (dg S c))⁻¹) : GL (Fin S.sum) K) :
        Matrix (Fin S.sum) (Fin S.sum) K) := by rw [cj_back]; exact hu
    exact (isUpUni_cj _ _).1 this
  · unfold fm
    simp only [cj_back]
end Formalism.FourierDecayAlt.P.KernelScalingBack
