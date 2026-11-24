-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.exp_mem_glev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:38:40.427065+00:00
-- url     : https://prove2.me/submissions/4445dea7-0d0c-4e2e-b3a8-1b86b461beef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_skew_real
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_exp_mem_UH
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_exp_fix

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (i : Fin (r + 1)) (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r))
    (hc : ∀ a : Fin r, a.val < i.val → ∀ x, X x (eI k r a) = 0 ∧ X x (esI k r a) = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  simp only [Glev, Set.mem_setOf_eq]
  refine ⟨exp_mem_UH _ (skew_real X hX t), fun a ha => ⟨exp_fix _ _ fun x => ?_, exp_fix _ _ fun x => ?_⟩⟩
  · rw [Matrix.smul_apply, (hc a ha x).1, smul_zero]
  · rw [Matrix.smul_apply, (hc a ha x).2, smul_zero]
end Formalism.FourierDecayAlt.Q.TInvW
