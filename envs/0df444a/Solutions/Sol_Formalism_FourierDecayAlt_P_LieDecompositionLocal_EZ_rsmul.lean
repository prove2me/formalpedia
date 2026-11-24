-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.EZ_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:25.212376+00:00
-- url     : https://prove2.me/submissions/56a50939-482e-4599-91b6-4314d790df7f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_antihermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hpart1_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hpart2_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_rsmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) (a : ℝ)
    (Z : Mat k r) : EZ ((a : ℂ) • Z) Φ g = (a : ℂ) • EZ Z Φ g := by
  have hd : (a : ℂ) • Z = (a : ℂ) • hpart1 (Hpk k r) Z + Complex.I • ((a : ℂ) • hpart2 (Hpk k r) Z) := by
    conv_lhs => rw [dec Z]
    rw [smul_add, smul_comm (a : ℂ) Complex.I]
  have hP := B4.inLie_rsmul (hermitian_part_mem_lie Z) a
  have hQ := B4.inLie_rsmul (antihermitian_part_mem_lie Z) a
  have e : EZ ((a : ℂ) • Z) Φ g = RdV ((a : ℂ) • hpart1 (Hpk k r) Z) Φ g +
      Complex.I • RdV ((a : ℂ) • hpart2 (Hpk k r) Z) Φ g := by
    unfold EZ; rw [hd, hpart1_dec hP hQ, hpart2_dec hP hQ]
  rw [e, rdV_rsmul hloc hgG (hermitian_part_mem_lie Z), rdV_rsmul hloc hgG (antihermitian_part_mem_lie Z)]
  unfold EZ
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_add, smul_comm (a : ℂ) Complex.I]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
