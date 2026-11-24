-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_hpart_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:06.359459+00:00
-- url     : https://prove2.me/submissions/f0f90aa3-3407-49c8-adf0-6c34aea55ca9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec

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
theorem _root_.solution {Z : Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (h1 : Z *ᵥ v = 0)
    (h2 : Zᴴ *ᵥ (Hpk k r *ᵥ v) = 0) :
    hpart1 (Hpk k r) Z *ᵥ v = 0 ∧ hpart2 (Hpk k r) Z *ᵥ v = 0 := by
  have hs : ∀ (c : ℂ) (A : Mx k r) (x : Fin (2 * r + k + 1) → ℂ), (c • A) *ᵥ x = c • (A *ᵥ x) := by
    intro c A x
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]
  have e : ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  unfold hpart1 hpart2
  constructor
  · rw [hs, Matrix.sub_mulVec, h1, e, sub_zero, smul_zero]
  · rw [hs, Matrix.add_mulVec, h1, e, add_zero, smul_zero]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
