-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.glev_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:17:36.631696+00:00
-- url     : https://prove2.me/submissions/e9b9260b-27ff-4225-a5c6-64e4dc010908

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_H_esI
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_H_eI
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_coord
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
    (hq : ∀ c, q ≠ posL k r i c) (v : Fin (2 * r + k + 1) → ℂ) : (g *ᵥ v) q = v q := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  obtain ⟨a, ha, hq'⟩ := outer q hq
  rcases hq' with rfl | rfl
  · exact coord hg'.1 (esI k r a) (eI k r a) (H_esI a) (hg'.2 a ha).2 v
  · exact coord hg'.1 (eI k r a) (esI k r a) (H_eI a) (hg'.2 a ha).1 v
end Formalism.FourierDecayAlt.Q.TInvW
