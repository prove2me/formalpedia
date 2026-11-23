-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.pX_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:40.699803+00:00
-- url     : https://prove2.me/submissions/581e4965-dea7-48a5-8bdc-85db09af5824

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution {I : Finset ℕ} {ρ : ℕ → ℂ} (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {R : ℂ[X]}
    (hR : ∀ l ∈ I, R.eval (-ρ l) = 0) : pX I ρ ∣ R := by
  unfold pX
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    show IsCoprime (X + C (ρ i)) (X + C (ρ j))
    have e : ∀ a : ℂ, (X + C a : ℂ[X]) = X - C (-a) := by intro a; simp
    rw [e, e]
    apply isCoprime_X_sub_C_of_isUnit_sub
    apply IsUnit.mk0
    intro h0
    exact hij (hinj i hi j hj (by linear_combination -h0))
  · intro l hl
    have e : (X + C (ρ l) : ℂ[X]) = X - C (-(ρ l)) := by rw [C_neg, sub_neg_eq_add]
    rw [e, dvd_iff_isRoot, IsRoot.def]
    exact hR l hl
end Formalism.FourierDecayAlt.P.Mx6.WB
