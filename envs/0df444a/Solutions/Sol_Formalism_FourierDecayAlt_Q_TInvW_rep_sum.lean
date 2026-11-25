-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.rep_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:58:37.414614+00:00
-- url     : https://prove2.me/submissions/e8642890-8beb-4cd5-bc73-67ddd8cfc5e9

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Mx k r → E}
    {x : ι → Sm E k r i D} (h : ∀ j, Rep (F j) (x j).1) :
    Rep (fun g => ∑ j, c j • F j g) (∑ j, c j • x j).1 := by
  intro g hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [h j g hg]
end Formalism.FourierDecayAlt.Q.TInvW
