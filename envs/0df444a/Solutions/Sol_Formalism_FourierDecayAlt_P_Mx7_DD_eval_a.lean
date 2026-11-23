-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.DD_eval_a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:43.105153+00:00
-- url     : https://prove2.me/submissions/35cbc376-506d-4e58-ad9a-2342be17c66b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_DD_eval

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
theorem _root_.solution (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) :
    (DD s ρ c q1 N M).eval (-ρ l) =
    c * q1.eval (-ρ l) + M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) := by
  rw [DD_eval]
  have z : ∏ j ∈ s, (-ρ l + ρ j) = 0 := Finset.prod_eq_zero hl (by ring)
  have z2 : (∑ m ∈ s, N m * ((∏ j ∈ s, (-ρ l + ρ j)) * ∏ j ∈ s.erase m, (-ρ l + (ρ j + 1)))) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [z]; ring)
  have z3 : (∑ m ∈ s, M m * ((∏ j ∈ s.erase m, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1)))) =
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) := by
    apply Finset.sum_eq_single l
    · intro j _ hj
      rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hj h.symm, hl⟩) (by ring)]; ring
    · intro h; exact absurd hl h
  rw [z2, z3, sub_zero]
end Formalism.FourierDecayAlt.P.Mx7
