-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.sum_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:19.685904+00:00
-- url     : https://prove2.me/submissions/51426065-1e9b-4a4b-9e8d-0c79b9e70226

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
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
variable {R : Type*} [Ring R] [Algebra ℂ R]
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (s : Finset ℕ) (D : ℕ → ℕ → M)
    (h : ∀ l ∈ s, ∀ j ∈ s, D l j + D j l = 0) : ∑ l ∈ s, ∑ j ∈ s, D l j = 0 := by
  have hc : ∑ l ∈ s, ∑ j ∈ s, D l j = ∑ l ∈ s, ∑ j ∈ s, D j l := Finset.sum_comm
  have h2 : ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D l j = 0 := by
    calc ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D l j
        = ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D j l := by rw [← hc]
      _ = ∑ l ∈ s, ∑ j ∈ s, (D l j + D j l) := by simp only [Finset.sum_add_distrib]
      _ = 0 := Finset.sum_eq_zero (fun l hl => Finset.sum_eq_zero (fun j hj => h l hl j hj))
  have h3 : (2 : ℂ) • ∑ l ∈ s, ∑ j ∈ s, D l j = 0 := by rw [two_smul]; exact h2
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
end Formalism.FourierDecayAlt.P.Mx7
