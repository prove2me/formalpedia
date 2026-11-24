-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.EZ_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:42.683907+00:00
-- url     : https://prove2.me/submissions/0550be7f-5283-4c24-b13e-be27984d793a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_antihermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hpart1_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hpart2_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_neg


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
theorem _root_.solution {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) (Z : Mat k r) :
    EZ (Complex.I • Z) Φ g = Complex.I • EZ Z Φ g := by
  have hd : Complex.I • Z = -hpart2 (Hpk k r) Z + Complex.I • hpart1 (Hpk k r) Z := by
    conv_lhs => rw [dec Z]
    rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
  have hP := B4.inLie_neg (antihermitian_part_mem_lie Z)
  have e : EZ (Complex.I • Z) Φ g = RdV (-hpart2 (Hpk k r) Z) Φ g +
      Complex.I • RdV (hpart1 (Hpk k r) Z) Φ g := by
    unfold EZ; rw [hd, hpart1_dec hP (hermitian_part_mem_lie Z), hpart2_dec hP (hermitian_part_mem_lie Z)]
  have hneg : RdV (-hpart2 (Hpk k r) Z) Φ g = -RdV (hpart2 (Hpk k r) Z) Φ g := by
    have := rdV_rsmul hloc hgG (antihermitian_part_mem_lie Z) (-1)
    simpa using this
  rw [e, hneg]
  unfold EZ
  rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
