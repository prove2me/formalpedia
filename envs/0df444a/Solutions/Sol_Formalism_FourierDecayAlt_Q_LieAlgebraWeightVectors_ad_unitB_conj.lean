-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_unitB_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:33.593802+00:00
-- url     : https://prove2.me/submissions/a371807e-dd4c-4d5e-b9be-99fba79444e4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_unitB_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_herm_g
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
theorem _root_.solution {g : Mx k r} (hg : gᴴ * Hpk k r * g = Hpk k r) (hgi : g * g⁻¹ = 1)
    {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m) :
    unitB (Hpk k r) (fun c => g *ᵥ Bs c) a b = g * unitB (Hpk k r) Bs a b * g⁻¹ := by
  have key : ∀ v, unitB (Hpk k r) (fun c => g *ᵥ Bs c) a b *ᵥ v =
      (g * unitB (Hpk k r) Bs a b * g⁻¹) *ᵥ v := by
    intro v
    rw [ad_unitB_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ad_unitB_mulVec, Matrix.mulVec_smul]
    congr 1
    conv_lhs => rw [show v = g *ᵥ (g⁻¹ *ᵥ v) by rw [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]]
    exact ad_herm_g hg _ _
  ext p q
  have := congrFun (key (Pi.single q 1)) p
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
