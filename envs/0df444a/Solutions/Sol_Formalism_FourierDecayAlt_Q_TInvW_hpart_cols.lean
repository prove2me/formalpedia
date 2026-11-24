-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.hpart_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:10.934856+00:00
-- url     : https://prove2.me/submissions/267e0d81-6c0a-4d49-94db-a8a039f24ca0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpk_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_unit_col
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_posL_ne

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
theorem _root_.solution (i : Fin (r + 1)) (p q : Fin (mdim k r i)) :
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) ∧
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) := by
  have key : ∀ a : Fin r, a.val < i.val → ∀ x c, (c = eI k r a ∨ c = esI k r a) →
      (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
    intro a ha x c hc
    obtain ⟨n1, n2⟩ := posL_ne i q a ha
    obtain ⟨z1, z2⟩ := hpk_zero i p a ha
    rcases hc with rfl | rfl
    · exact unit_col i p q _ n1 z1 x
    · exact unit_col i p q _ n2 z2 x
  refine ⟨fun a ha x => ?_, fun a ha x => ?_⟩ <;>
  · obtain ⟨e1, e2⟩ := key a ha x _ (Or.inl rfl)
    obtain ⟨e3, e4⟩ := key a ha x _ (Or.inr rfl)
    simp only [hpart1, hpart2]
    rw [hpk_inv]
    refine ⟨?_, ?_⟩ <;>
    · first
      | rw [Matrix.smul_apply, Matrix.sub_apply]
      | rw [Matrix.smul_apply, Matrix.add_apply]
      simp only [e1, e2, e3, e4, sub_zero, add_zero, smul_zero]
end Formalism.FourierDecayAlt.Q.TInvW
