-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.mem_supp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:06:42.522437+00:00
-- url     : https://prove2.me/submissions/b3da92f5-376d-4497-bdc1-bd88ff5f0036

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_isWeightOf_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_genH_support
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_wExp_eq_wt
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (last : Bool) (m : Fin n) (hm : if last then m.val + 1 = n else m.val = 0)
    (G : MvPolynomial (LVar ι ζ n) k) (j : ℤ) :
    j ∈ (genAct k isVec S last G).coeff.support ↔ ∃ ν, IsWeightOf isVec S (genSpace isVec S G) ν ∧ ν m = j := by
  rw [gen_mem_supp]
  constructor
  · rintro ⟨e, he, hj⟩
    exact ⟨wt isVec S e, (isWeightOf_iff isVec S G _).mpr ⟨e, (genH_support isVec S G e).mp he, rfl⟩,
      (wExp_eq_wt isVec S last m hm e).symm.trans hj⟩
  · rintro ⟨ν, hν, hj⟩
    obtain ⟨e, he, rfl⟩ := (isWeightOf_iff isVec S G _).mp hν
    exact ⟨e, (genH_support isVec S G e).mpr he, (wExp_eq_wt isVec S last m hm e).trans hj⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
