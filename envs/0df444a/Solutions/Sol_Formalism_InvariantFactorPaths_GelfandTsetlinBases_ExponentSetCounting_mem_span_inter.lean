-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.mem_span_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:47:21.607006+00:00
-- url     : https://prove2.me/submissions/f89db8cf-226d-4305-a9bf-feef740e3591

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
theorem _root_.solution {k V ι κ : Type*} [Field k] [AddCommGroup V] [Module k V] {v : ι → V}
    (hv : LinearIndependent k v) (A : κ → Set ι) (i₀ : κ) (G : V)
    (h : ∀ i, G ∈ Submodule.span k (v '' A i)) : G ∈ Submodule.span k (v '' {x | ∀ i, x ∈ A i}) := by
  have h' : ∀ i, ∃ l ∈ Finsupp.supported k k (A i), Finsupp.linearCombination k v l = G := by
    intro i
    have hi := h i
    rw [Finsupp.mem_span_image_iff_linearCombination] at hi
    exact hi
  choose l hl hlG using h'
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨l i₀, ?_, hlG i₀⟩
  rw [Finsupp.mem_supported]
  intro x hx i
  have e : l i = l i₀ := hv ((hlG i).trans (hlG i₀).symm)
  have hs := (Finsupp.mem_supported k (l i)).mp (hl i)
  exact hs (by rw [e]; exact hx)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
