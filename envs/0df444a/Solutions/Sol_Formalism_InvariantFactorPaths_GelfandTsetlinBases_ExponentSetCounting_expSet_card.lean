-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.expSet_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:03:17.760792+00:00
-- url     : https://prove2.me/submissions/77483758-9f9e-4b76-a660-fee490984361

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_expSet_subset

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
theorem _root_.solution (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) :
    (expSet n i N B).ncard ≤ ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  have hfin : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.Finite :=
    (hR n (N - i) (fun j => B (i + j))).2.1
  have hcard : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard =
      ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) :=
    (hR n (N - i) (fun j => B (i + j))).1
  calc (expSet n i N B).ncard
      ≤ ((Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2))) ''
          {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}).ncard :=
        Set.ncard_le_ncard (expSet_subset n i N B) (hfin.image _)
    _ ≤ {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard :=
        Set.ncard_image_le hfin
    _ = ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) := hcard
    _ = ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) :=
        (Finset.prod_Ico_eq_prod_range (fun l => (n + B l - 1).choose (B l)) i N).symm
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
