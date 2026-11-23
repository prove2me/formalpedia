-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.dl_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:16.115804+00:00
-- url     : https://prove2.me/submissions/04bcfabd-bdb8-41c0-bdbd-18beefbcbbbf

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_map_le_of_int
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
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution {M N : Matrix ι ι K} (hMN : M * N = 1) (hM : ∀ i j, M i j ∈ R)
    (hN : ∀ i j, N i j ∈ R) : dl R M = 1 := by
  have h1 := map_le_of_int (ι := ι) hM
  have h2 : LL R ι ≤ (LL R ι).map (mv M) := by
    intro v hv
    refine AddSubgroup.mem_map.mpr ⟨N *ᵥ v, ?_, ?_⟩
    · exact map_le_of_int hN (AddSubgroup.mem_map.mpr ⟨v, hv, rfl⟩)
    · simp [Matrix.mulVec_mulVec, hMN]
  unfold dl
  rw [le_antisymm h1 h2, gi_self]
end Formalism.FourierDecayAlt.P.A5x5
