-- Prove2me | solution 1 for CountingMatroid.Analysis.FeasibilitySolver.commonBaseCount_pos_iff_common_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:52:28.644011+00:00
-- url     : https://prove2.me/submissions/13c38545-f894-4299-bab3-d927f9b8bda7

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
import Definitions.Def_CountingMatroid_Analysis_ExchangeWalkReversal
import Definitions.Def_CountingMatroid_Analysis_FeasibilitySolver
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Analysis_RankOneFeasibility
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
namespace CountingMatroid.Analysis.FoundPathAugmentation
end CountingMatroid.Analysis.FoundPathAugmentation
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
namespace CountingMatroid.Analysis.FindPathCertificate
end CountingMatroid.Analysis.FindPathCertificate
namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
namespace CountingMatroid.Analysis.NoPathSeparator
end CountingMatroid.Analysis.NoPathSeparator
namespace CountingMatroid.Analysis.ExchangeClosedBasis
end CountingMatroid.Analysis.ExchangeClosedBasis
set_option autoImplicit false

/-!
The common-base predicate is connected to the paper's feasibility pretest.
Ranks zero and one are implemented and verified using the charged interface;
the rank-one implementation is the first augmentation from the empty set.
An explicit capped exchange-graph implementation handles arbitrary rank.
Its uniform cost certificate is proved. The parent now reduces correctness to
the augmentation-progress obligation in a separate child file, which remains
open. The parent proof has no open tactic goals but depends on that obligation.
-/

namespace CountingMatroid.Analysis.FeasibilitySolver
end CountingMatroid.Analysis.FeasibilitySolver
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines
open CountingMatroid.Model
open scoped Classical

/-- INTERNAL: Bridge the counted common-base predicate to the size-`r`
common-independent-set predicate used by the cited intersection algorithm.
TEXLINE: main.tex:278-289 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (hr : CommonRank r M₁ M₂) :
    0 < commonBaseCount M₁ M₂ ↔
      ∃ I : Finset (Fin n), I.card = r ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by
  classical
  constructor
  · intro h
    obtain ⟨I, hI⟩ : (commonBases M₁ M₂).Nonempty := by
      simpa only [commonBaseCount, Finset.card_pos] using h
    have hB : M₁.IsBase (I : Set (Fin n)) ∧ M₂.IsBase (I : Set (Fin n)) := by
      simpa only [commonBases, Finset.mem_filter, Finset.mem_univ, true_and] using hI
    refine ⟨I, ?_, hB.1.indep, hB.2.indep⟩
    have hcard := hB.1.encard_eq_eRank
    simpa [hr.1] using hcard
  · rintro ⟨I, hcard, hI₁, hI₂⟩
    have hB₁ : M₁.IsBase (I : Set (Fin n)) := by
      apply hI₁.isBase_of_eRk_ge I.finite_toSet
      rw [hI₁.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hcard, hr.1]
    have hB₂ : M₂.IsBase (I : Set (Fin n)) := by
      apply hI₂.isBase_of_eRk_ge I.finite_toSet
      rw [hI₂.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hcard, hr.2]
    apply Finset.card_pos.mpr
    exact ⟨I, by simpa [commonBases] using And.intro hB₁ hB₂⟩
