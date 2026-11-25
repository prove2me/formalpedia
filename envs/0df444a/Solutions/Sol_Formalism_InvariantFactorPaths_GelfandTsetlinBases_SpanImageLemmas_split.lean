-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas.split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:06:49.751744+00:00
-- url     : https://prove2.me/submissions/9762c255-9c98-435d-91c3-dfc373c12c5d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_MemSpanImageIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas
theorem _root_.solution {X R : Type} [CommRing R] (a : X →₀ R) (S : Set X) :
    ∃ a1 a2 : X →₀ R, a = a1 + a2 ∧ (∀ x ∉ S, a1 x = 0) ∧ (∀ x ∈ S, a2 x = 0) ∧ ∀ x ∉ S, a2 x = a x := by
  classical
  refine ⟨a.filter (· ∈ S), a.filter (fun x => ¬ x ∈ S), (Finsupp.filter_add_filter_not a _).symm, ?_, ?_, ?_⟩
  · intro x hx
    exact Finsupp.filter_apply_neg _ _ hx
  · intro x hx
    exact Finsupp.filter_apply_neg _ _ (not_not.mpr hx)
  · intro x hx
    exact Finsupp.filter_apply_pos _ _ hx
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SpanImageLemmas
