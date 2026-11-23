-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.pa_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:59.358207+00:00
-- url     : https://prove2.me/submissions/96cd1cf4-ae99-44a4-8c00-3548ee803686

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j) (F : ℂ[X])
    (h : ∀ l ∈ s, F.eval (-ρ l) = 0) : pa s ρ ∣ F := by
  unfold pa
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
    have e : (X + C (ρ l) : ℂ[X]) = X - C (-ρ l) := by simp
    rw [e, dvd_iff_isRoot]
    exact h l hl
end Formalism.FourierDecayAlt.P.Mx7
