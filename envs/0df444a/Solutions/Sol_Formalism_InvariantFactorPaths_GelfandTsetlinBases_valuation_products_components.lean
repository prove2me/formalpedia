-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.valuation_products_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:52.961194+00:00
-- url     : https://prove2.me/submissions/67f1bb0b-fba5-4e6d-af64-f47f30d6a74c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_psi_bound
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_gen_mem_supp


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
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : ValuationProductsComponents := by
  intro k _ n N i isVec B μ I hp hI hi
  constructor
  · intro m hm
    unfold valS
    refine Finset.le_min fun j hj => ?_
    obtain ⟨e, he, rfl⟩ := (gen_mem_supp isVec _ true _ j).1 hj
    have := A0.psi_bound (k := k) hp hI hi (S := {j : ℕ | j < i}) (fun j => Iff.rfl) true m
      (by simpa using hm) e he
    simp only [A0.sgn, if_true, one_mul] at this
    exact WithTop.coe_le_coe.2 this
  · intro m hm
    unfold lam1S
    refine Finset.max_le fun j hj => ?_
    obtain ⟨e, he, rfl⟩ := (gen_mem_supp isVec _ false _ j).1 hj
    have := A0.psi_bound (k := k) hp hI hi (S := {j : ℕ | j < i}) (fun j => Iff.rfl) false m
      (by simpa using hm) e he
    simp only [A0.sgn, Bool.false_eq_true, if_false] at this
    exact WithBot.coe_le_coe.2 (by linarith)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
