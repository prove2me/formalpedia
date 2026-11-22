-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.LL_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:41:17.290893+00:00
-- url     : https://prove2.me/submissions/b7a033c3-fc60-409c-834e-e2bb3808650c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {σ τ : Type*} [LinearOrder τ] (κ : σ → τ)
variable {κ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution (hκ : Function.Injective κ) {e e' e'' : σ →₀ ℕ} (h : LL κ e e') (h' : LL κ e' e'') :
    LL κ e e'' := by
  obtain ⟨x, hx, hxy⟩ := h
  obtain ⟨x', hx', hxy'⟩ := h'
  rcases lt_trichotomy (κ x) (κ x') with hlt | heq | hgt
  · refine ⟨x, ?_, fun y hy => ?_⟩
    · rw [← hxy' x hlt]; exact hx
    · rw [hxy y hy, hxy' y (hy.trans hlt)]
  · have : x = x' := hκ heq
    subst this
    exact ⟨x, hx.trans hx', fun y hy => by rw [hxy y hy, hxy' y hy]⟩
  · refine ⟨x', ?_, fun y hy => ?_⟩
    · rw [hxy x' hgt]; exact hx'
    · rw [hxy y (hy.trans hgt), hxy' y hy]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
