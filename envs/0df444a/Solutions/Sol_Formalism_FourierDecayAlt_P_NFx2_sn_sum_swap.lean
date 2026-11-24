-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_sum_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:25.878652+00:00
-- url     : https://prove2.me/submissions/177b9151-2199-496a-ad82-e126fa1832b2

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (s : Finset ℕ) (F : ℕ → ℕ → A) :
    ∑ j ∈ s, ∑ l ∈ s.erase j, F l j = ∑ l ∈ s, ∑ j ∈ s.erase l, F l j := by
  have h1 : ∀ j, ∑ l ∈ s.erase j, F l j = ∑ l ∈ s, if l ≠ j then F l j else 0 := fun j => by
    rw [← Finset.sum_filter, Finset.filter_ne']
  have h2 : ∀ l, ∑ j ∈ s.erase l, F l j = ∑ j ∈ s, if j ≠ l then F l j else 0 := fun l => by
    rw [← Finset.sum_filter, Finset.filter_ne']
  simp_rw [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  simp [ne_comm]
end Formalism.FourierDecayAlt.P.NFx2
