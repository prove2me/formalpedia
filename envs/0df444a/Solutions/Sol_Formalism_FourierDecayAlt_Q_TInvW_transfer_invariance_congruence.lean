-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.transfer_invariance_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:22:21.895472+00:00
-- url     : https://prove2.me/submissions/913846cd-e67c-4cf9-a597-fbe9c645449d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_exp_hpart1_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_exp_hpart2_mem
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_mul__c26af469cc3a


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
theorem _root_.solution : StepCongr := by
  intro E _ _ k r i D a b f f' g hD hg hff
  have key : ∀ X : Mx k r, (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) →
      RdV X f g = RdV X f' g := by
    intro X hX
    unfold RdV
    apply Filter.EventuallyEq.deriv_eq
    have hγ := hasDerivAt_mul_exp_smul_zero g X
    have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp [NormedSpace.exp_zero]
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ D :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hD.mem_nhds hg.2)
    filter_upwards [hmem] with t ht
    exact hff _ ⟨glev_mul' hg.1 (hX t), ht⟩
  show RdV _ f g + Complex.I • RdV _ f g = RdV _ f' g + Complex.I • RdV _ f' g
  rw [key _ (exp_hpart1_mem i a b), key _ (exp_hpart2_mem i a b)]
end Formalism.FourierDecayAlt.Q.TInvW
