-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.a3one_of_factSplit_of_countCont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:10.464111+00:00
-- url     : https://prove2.me/submissions/dc176b59-c92b-485e-8130-03381176fa7f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_card_good
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_expSet_finite
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_expSet_card
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_psiFam_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_psiFam_good
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_mem_spanProd

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
theorem _root_.solution (hI : LemmaA2indep) (hfin : PathIdxFinite) (hR : PolBRank) (hT : LemmaA3top) (hF : FactSplit)
    (hC : CountCont) : LemmaA3one := by
  intro k _ n N i isVec B θ M G hn hi hG hg
  classical
  set S : Set (PathIdx n N isVec B) := {x | GoodW θ M (x.1.1 i)} with hS
  have hli : LinearIndependent k (psiFam k n N isVec B) := hI k n N isVec B
  haveI : Finite (PathIdx n N isVec B) := hfin n N isVec B
  haveI : Finite (PathIdx n i isVec B) := hfin n i isVec B
  haveI : Finite (expSet n i N B) := (expSet_finite hR n i N B).to_subtype
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Fintype ({x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} × expSet n i N B) :=
    Fintype.ofFinite _
  have hle : Submodule.span k (psiFam k n N isVec B '' S) ≤
      Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_spanProd hT hF k hn hi isVec B θ M _ (psiFam_mem k N isVec B x)
      (psiFam_good k hn hi isVec B θ M x hx)
  haveI hfd : FiniteDimensional k (Submodule.span k (Set.range (prodFam k n i N isVec B θ M))) := by
    first
      | exact FiniteDimensional.span_of_finite k (Set.finite_range _)
      | exact FiniteDimensional.span_of_finite (Set.finite_range _)
      | exact Module.Finite.span_of_finite k (Set.finite_range _)
      | infer_instance
  have hr1 : Module.finrank k (Submodule.span k (Set.range (prodFam k n i N isVec B θ M))) ≤
      Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} := by
    calc Module.finrank k (Submodule.span k (Set.range (prodFam k n i N isVec B θ M)))
        ≤ Fintype.card ({x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} × expSet n i N B) :=
          finrank_range_le_card (b := prodFam k n i N isVec B θ M)
      _ = Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} * Nat.card (expSet n i N B) := by
          rw [← Nat.card_eq_fintype_card, Nat.card_prod]
      _ ≤ Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} *
            ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) :=
          Nat.mul_le_mul le_rfl (by
            first
              | (rw [Nat.card_coe_set_eq]; exact expSet_card hR n i N B)
              | exact expSet_card hR n i N B)
      _ = Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} :=
          (card_good hC hi isVec B θ M).symm
  have hr2 : Module.finrank k (Submodule.span k (psiFam k n N isVec B '' S)) =
      Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} := by
    have h := finrank_span_eq_card
      (hli.comp (Subtype.val : S → PathIdx n N isVec B) Subtype.val_injective)
    rw [Set.range_comp, Subtype.range_coe, ← Nat.card_eq_fintype_card] at h
    exact h
  have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [hr2]; exact hr1)
  rw [heq]
  exact mem_spanProd hT hF k hn hi isVec B θ M G hG hg
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
