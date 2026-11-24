-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.glev_fix_outer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:22.988201+00:00
-- url     : https://prove2.me/submissions/07fae638-8abc-473c-8863-8ef6e3524315

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_outer

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
theorem _root_.solution {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g *ᵥ bvec q = bvec q := by
  obtain ⟨a, ha, hq'⟩ := outer q hq
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  rcases hq' with rfl | rfl
  · exact (hg'.2 a ha).1
  · exact (hg'.2 a ha).2
end Formalism.FourierDecayAlt.Q.TInvW
