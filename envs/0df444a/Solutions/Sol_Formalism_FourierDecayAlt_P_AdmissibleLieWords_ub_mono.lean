-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:18.235664+00:00
-- url     : https://prove2.me/submissions/68035e1c-2c32-4270-a4f6-3e68cf04237c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {f : Mat k r → E} {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n : ℕ} {C : ℝ} {e γ e' γ' : ℕ}
    (h : UB f S n C e γ) (hC : 0 ≤ C) (he : e ≤ e') (hγ : γ ≤ γ') : UB f S n C e' γ' := by
  intro w hw g hg
  have h1 := gN_ge_one (hSG hg)
  refine (h w hw g hg).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact pow_le_pow_right₀ h1 (Nat.add_le_add he (Nat.mul_le_mul_right _ hγ))
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
