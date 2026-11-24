-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_unitB_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:34.581193+00:00
-- url     : https://prove2.me/submissions/b05c990a-3477-40c0-8009-8af8b00c1e85

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_unitB_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_unitB_ct_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_hpart_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    {v : Fin (2 * r + k + 1) → ℂ} (ha : herm (Hpk k r) v (Bs a) = 0) (hb : herm (Hpk k r) v (Bs b) = 0) :
    hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 ∧ hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 := by
  apply ad_hpart_kill
  · rw [ad_unitB_mulVec, hb, zero_smul]
  · rw [ad_unitB_ct_mulVec, ha, zero_smul]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
