-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.finsum_ite_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:05.463678+00:00
-- url     : https://prove2.me/submissions/611006ea-f5a5-4546-b508-1e7a20c64c5b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
namespace Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
theorem _root_.solution {α : Type} (S : Finset α) (p : α → Prop) [DecidablePred p] (f : α → ℂ)
    (hS : ∀ x, p x → x ∈ S) :
    ∑ᶠ x, (if p x then f x else 0) = ∑ x ∈ S, if p x then f x else 0 := by
  refine finsum_eq_sum_of_support_subset _ ?_
  intro x hx
  by_cases hp : p x
  · exact hS x hp
  · simp [hp] at hx
end Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
