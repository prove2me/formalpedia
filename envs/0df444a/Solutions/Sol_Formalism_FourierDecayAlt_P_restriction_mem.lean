-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.restriction_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:27:47.278558+00:00
-- url     : https://prove2.me/submissions/e89025f5-3959-4f2c-a70f-c2e504437b42

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_weyl_cell_mem_level_group
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_w1_commute_of_mem_Glev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_weyl_cell_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_slev_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_slev_glev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_ffl_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_fam_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cd_normPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.ResMem := by
  intro Wp Wq _ _ _ _ k r z z' π π' l D _ _ hD J hJ
  have hle : l.castSucc ≤ l.succ := by
    rw [Fin.le_def]
    simp
  refine ⟨fun c hc => ⟨⟨hD.1.preimage (Qx3.mulLeftL (w1 k r l c)).continuous, ?_⟩,
    Qx3.ffl_res hle (Qx3.weyl_cell_mem_level_group l hc) (fun g hg => Qx3.w1_commute_of_mem_Glev l c hg) hJ⟩, ?_⟩
  · intro g hg s hs s' hs'
    show w1 k r l c * (s * g * s') ∈ D
    have e : w1 k r l c * (s * g * s') = s * (w1 k r l c * g) * s' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Qx3.w1_commute_of_mem_Glev l c (Qx3.slev_glev _ hs),
        Matrix.mul_assoc s (w1 k r l c) g]
    rw [e]
    exact hD.2 _ ⟨Qx3.glev_mul (Qx3.weyl_cell_mem_level_group l hc) (Qx3.glev_mono hle hg.1), hg.2⟩ s (Qx3.slev_mono hle hs) s'
      (Qx3.slev_mono hle hs')
  · exact Qx3.fam_res hle (w := fun c => w1 k r l (c l))
      (ρ := fun c => ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ)) (Qx3.weyl_cell_contDiffOn l)
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (Qx3.cd_normPow l _))
      (fun c hc => Qx3.weyl_cell_mem_level_group l (hc l)) (fun c _ g hg => Qx3.w1_commute_of_mem_Glev l (c l) hg) hJ
end Formalism.FourierDecayAlt.P
