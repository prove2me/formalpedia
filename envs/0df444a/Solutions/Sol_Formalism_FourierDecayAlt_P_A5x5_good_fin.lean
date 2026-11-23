-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.good_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:49.990533+00:00
-- url     : https://prove2.me/submissions/93a8219a-7de8-4009-8d6b-abb0f4c6759c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_dl_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_good_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_good_equiv
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (hd : LocalDatum K R ψ) : ∀ n : ℕ, Good R (Fin n)
  | 0 => by
    intro M _
    rw [det_isEmpty, modK_one]
    exact dl_eq_one (N := 1) (Subsingleton.elim _ _) (fun i => i.elim0) (fun i => i.elim0)
  | n + 1 =>
    good_equiv (Fintype.equivOfCardEq (by simp)) (good_step hd (solution hd n))
end Formalism.FourierDecayAlt.P.A5x5
