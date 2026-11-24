-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.H_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:21.659172+00:00
-- url     : https://prove2.me/submissions/54fa6f9f-3d25-48f6-b2f2-660cab55d486

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
theorem _root_.solution (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (eI k r a) = w (esI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (esI k r a)]
  · have h1 : Hpk k r (eI k r a) (esI k r a) = 1 := by
      simp only [Hpk, eI, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * r + k - a.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have h0 : Hpk k r (eI k r a) j = 0 := by
      simp only [Hpk, eI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.Q.TInvW
