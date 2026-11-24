-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:20.706332+00:00
-- url     : https://prove2.me/submissions/c63f7480-f4de-4409-9790-c5b05028e233

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (c d : Fin (2 * r + k + 1))
    (hcd : ∀ w, (Hpk k r *ᵥ w) c = w d) (hfix : g *ᵥ bvec c = bvec c) (v : Fin (2 * r + k + 1) → ℂ) :
    (g *ᵥ v) d = v d := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  have hcol : ∀ l, g l c = bvec c l := fun l => by
    rw [← congrFun hfix l]
    simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  have hrow : ∀ j, (Hpk k r * g) c j = Hpk k r c j := by
    intro j
    have h1 := congrFun (congrFun hU c) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at h1
    rw [← h1, Finset.sum_eq_single c]
    · rw [conjTranspose_apply, hcol]
      simp [bvec]
    · intro l _ hl
      rw [conjTranspose_apply, hcol]
      simp [bvec, Pi.single_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have key : (Hpk k r *ᵥ (g *ᵥ v)) c = (Hpk k r *ᵥ v) c := by
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, hrow]
  calc (g *ᵥ v) d = (Hpk k r *ᵥ (g *ᵥ v)) c := (hcd _).symm
    _ = (Hpk k r *ᵥ v) c := key
    _ = v d := hcd v
end Formalism.FourierDecayAlt.Q.TInvW
