-- Prove2me | solution 1 for CountingMatroid.Analysis.IntersectionAugmentation.separator_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:52:12.786265+00:00
-- url     : https://prove2.me/submissions/52392d7d-7ebd-456b-b57a-02c71a32ff1f

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
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
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

namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
namespace CountingMatroid.Analysis.FoundPathAugmentation
end CountingMatroid.Analysis.FoundPathAugmentation
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
namespace Arlib
end Arlib
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
The augmentation-progress proof combines exact exchange-query predicates,
a graph separator when search fails, and shortest-path exchange preservation
when search succeeds. The matroid basis certificates on both sides of the
separator are proved here using `ExchangeClosedBasis`. Graph-search saturation
is proved in `NoPathSeparator`; successful-path preservation remains an
explicit obligation in `FoundPathAugmentation`. This is an internal refinement
of the cited pretest, not an additional oracle or an assumed contract.
-/

namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.IntersectionAugmentation

open CountingMatroid.Model CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: Two complementary rank certificates bound every common
independent competitor. This is the last arithmetic step of the no-path
maximality argument; graph nonreachability must establish the two bases.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (I R : Finset (Fin n))
    (hfirst : M₁.IsBasis ((I \ R : Finset (Fin n)) : Set (Fin n))
      ((Finset.univ \ R : Finset (Fin n)) : Set (Fin n)))
    (hsecond : M₂.IsBasis ((I ∩ R : Finset (Fin n)) : Set (Fin n))
      (R : Set (Fin n)))
    (J : Finset (Fin n)) (hJ₁ : M₁.Indep (J : Set (Fin n)))
    (hJ₂ : M₂.Indep (J : Set (Fin n))) : J.card ≤ I.card := by
  have hdiffIndep : M₁.Indep ((J \ R : Finset (Fin n)) : Set (Fin n)) :=
    hJ₁.subset (by simp only [Finset.coe_sdiff]; exact Set.sdiff_subset)
  have hdiffSubset : ((J \ R : Finset (Fin n)) : Set (Fin n)) ⊆
      ((Finset.univ \ R : Finset (Fin n)) : Set (Fin n)) := by
    intro i hi
    change i ∈ J \ R at hi
    change i ∈ Finset.univ \ R
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
  have hdiff := hdiffIndep.encard_le_eRk_of_subset hdiffSubset
  rw [← hfirst.encard_eq_eRk] at hdiff
  have hdiffCard : (J \ R).card ≤ (I \ R).card := by
    simpa only [Set.encard_coe_eq_coe_finsetCard, ENat.coe_le_coe] using hdiff
  have hinterIndep : M₂.Indep ((J ∩ R : Finset (Fin n)) : Set (Fin n)) :=
    hJ₂.subset (by simp only [Finset.coe_inter]; exact Set.inter_subset_left)
  have hinter := hinterIndep.encard_le_eRk_of_subset
    (show ((J ∩ R : Finset (Fin n)) : Set (Fin n)) ⊆ (R : Set (Fin n)) by
      simp only [Finset.coe_inter]; exact Set.inter_subset_right)
  rw [← hsecond.encard_eq_eRk] at hinter
  have hinterCard : (J ∩ R).card ≤ (I ∩ R).card := by
    simpa only [Set.encard_coe_eq_coe_finsetCard, ENat.coe_le_coe] using hinter
  have hJpart := Finset.card_sdiff_add_card_inter J R
  have hIpart := Finset.card_sdiff_add_card_inter I R
  omega
