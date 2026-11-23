-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.mulR_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:00.582962+00:00
-- url     : https://prove2.me/submissions/dd67a60e-5ce7-4ebb-83e0-4b7b794a8899

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
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



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) (d e : K) (hd : d ∈ R) (he : e ∈ R)
    (hde : d * e = 1) : mulR R d = R.toAddSubgroup := by
  unfold mulR
  ext z
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact R.mul_mem hd hy
  · intro hz
    exact ⟨e * z, R.mul_mem he hz, by rw [← mul_assoc, hde, one_mul]⟩
end Formalism.FourierDecayAlt.P.A5x6
