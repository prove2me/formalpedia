-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.good_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:15:52.928159+00:00
-- url     : https://prove2.me/submissions/4eb34ccf-c210-4304-9acb-0ae527ba4c42

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_cornerValSubmodule


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
theorem _root_.solution (k : Type) [Field k] (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) (c : k)
    (G H : MvPolynomial (ℕ × Fin n) k) (hG : GoodG isVec i θ M G) (hH : GoodG isVec i θ M H) :
    GoodG isVec i θ M (c • G + H) := by
  constructor
  · intro t ht
    have h := (cornerValSubmodule k ℕ Empty n isVec {j : ℕ | j < i} (t : WithTop ℤ) ⊥ c (rename Sum.inl G)
      (rename Sum.inl H)).1 (hG.1 t ht) (hH.1 t ht)
    rw [valP, map_add, map_smul]
    exact h
  · intro t ht
    have h := (cornerValSubmodule k ℕ Empty n isVec {j : ℕ | j < i} ⊤ (t : WithBot ℤ) c (rename Sum.inl G)
      (rename Sum.inl H)).2 (hG.2 t ht) (hH.2 t ht)
    rw [lamP, map_add, map_smul]
    exact h
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
