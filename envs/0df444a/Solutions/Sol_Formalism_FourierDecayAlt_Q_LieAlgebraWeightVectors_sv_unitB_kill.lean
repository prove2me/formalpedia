-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_unitB_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:02:26.47447+00:00
-- url     : https://prove2.me/submissions/153773a4-84fb-40d8-bb0a-863befc52246

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_unitB_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_unitB_adj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_inv


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    {v : Fin (2 * r + k + 1) → ℂ} (ha : herm (Hpk k r) v (Bs a) = 0) (hb : herm (Hpk k r) v (Bs b) = 0) :
    hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 ∧ hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 := by
  have e1 : unitB (Hpk k r) Bs a b *ᵥ v = 0 := by rw [sv_unitB_mulVec, hb, zero_smul]
  have e2 : (Hpk k r * (unitB (Hpk k r) Bs a b)ᴴ * Hpk k r) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sv_unitB_adj, ha, zero_smul, Matrix.mulVec_zero]
  unfold hpart1 hpart2
  rw [Qx2.hpk_inv, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec, e1, e2]
  simp only [sub_self, add_zero, smul_zero, and_self]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
