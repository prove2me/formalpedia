-- Prove2me | solution 1 for CountingMatroid.Analysis.RankWeightSupportExchange.rank_weight_support_exchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:27:52.666722+00:00
-- url     : https://prove2.me/submissions/8ddfe291-505f-4728-9dec-2a656c4ebb2f

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_CountingMatroid_Analysis_RankWeightSupportExchange_rank_weight_mem_support_iff

namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
section


set_option autoImplicit false

/-! The subset exponent description of the rank-weight polynomial support.
The exchange condition depends only on the subsets, not on matroid ranks. -/

namespace CountingMatroid.Analysis.RankWeightSupportExchange

open scoped BigOperators
open LorentzianDirectionalSignature



/-- INTERNAL: The homogenizing coordinate records the complement cardinality. -/
theorem subsetExponent_none {α : Type} [Fintype α] (A : Finset α) :
    subsetExponent A none = Fintype.card α - A.card := by
  classical
  simp [subsetExponent]

/-- INTERNAL: Each label coordinate is the subset's membership indicator. -/
theorem subsetExponent_some {α : Type} [Fintype α] [DecidableEq α]
    (A : Finset α) (a : α) : subsetExponent A (some a) = if a ∈ A then 1 else 0 := by
  classical
  simp [subsetExponent, Finsupp.single_apply, eq_comm]









end CountingMatroid.Analysis.RankWeightSupportExchange

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · identified the support with all subset exponents and proved unit exchange by insert, erase, and swap; the argument needs only positive coefficients and no matroid exchange or rank-signature theorem.
-/

end
set_option autoImplicit false

/-! The subset exponent description of the rank-weight polynomial support.
The exchange condition depends only on the subsets, not on matroid ranks. -/

namespace CountingMatroid.Analysis.RankWeightSupportExchange
end CountingMatroid.Analysis.RankWeightSupportExchange
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightSupportExchange

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: The full subset support admits transfer of a unit from a larger
coordinate to a smaller one. TEXLINE: main.tex:334-339 -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) :
    HasMConvexSupport (∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)) := by
  classical
  intro x hx y hy i hi
  obtain ⟨A, rfl⟩ := (rank_weight_mem_support_iff N q hq x).mp hx
  obtain ⟨B, rfl⟩ := (rank_weight_mem_support_iff N q hq y).mp hy
  cases i with
  | none =>
    simp only [subsetExponent_none] at hi
    have hAB : A.card < B.card := by omega
    obtain ⟨b, hbB, hbA⟩ := Finset.exists_mem_notMem_of_card_lt_card hAB
    refine ⟨some b, ?_, ?_⟩
    · simp [subsetExponent_some, hbA, hbB]
    · apply (rank_weight_mem_support_iff N q hq _).mpr
      refine ⟨insert b A, ?_⟩
      ext s
      cases s with
      | none =>
        have hbound := (insert b A).card_le_univ
        rw [Finset.card_insert_of_notMem hbA] at hbound
        simp [subsetExponent_none,
          Finset.card_insert_of_notMem hbA]
        omega
      | some c =>
        by_cases hcb : c = b
        · subst c; simp [subsetExponent_some, hbA]
        · simp [subsetExponent_some, hcb]
  | some a =>
    simp only [subsetExponent_some] at hi
    have haA : a ∈ A := by split_ifs at hi <;> omega
    have haB : a ∉ B := by split_ifs at hi <;> omega
    by_cases hnone : subsetExponent A none < subsetExponent B none
    · refine ⟨none, hnone, ?_⟩
      apply (rank_weight_mem_support_iff N q hq _).mpr
      refine ⟨A.erase a, ?_⟩
      ext s
      cases s with
      | none =>
        have hbound := A.card_le_univ
        have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨a, haA⟩)
        simp [subsetExponent_none, Finset.card_erase_of_mem haA]
        omega
      | some c =>
        by_cases hca : c = a
        · subst c; simp [subsetExponent_some, haA]
        · simp [subsetExponent_some, hca]
    · have hAB : A.card ≤ B.card := by
        simp only [subsetExponent_none] at hnone
        have hA := A.card_le_univ
        have hB := B.card_le_univ
        omega
      have hlt : (A.erase a).card < B.card := by
        rw [Finset.card_erase_of_mem haA]
        have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨a, haA⟩)
        omega
      obtain ⟨b, hbB, hbErase⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      have hba : b ≠ a := by intro h; subst b; exact haB hbB
      have hbA : b ∉ A := by
        intro hb
        exact hbErase (Finset.mem_erase.mpr ⟨hba, hb⟩)
      refine ⟨some b, ?_, ?_⟩
      · simp [subsetExponent_some, hbA, hbB]
      · apply (rank_weight_mem_support_iff N q hq _).mpr
        refine ⟨insert b (A.erase a), ?_⟩
        ext s
        cases s with
        | none =>
          have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨a, haA⟩)
          simp [subsetExponent_none,
            Finset.card_insert_of_notMem hbErase, Finset.card_erase_of_mem haA]
          omega
        | some c =>
          by_cases hca : c = a <;> by_cases hcb : c = b <;>
            simp_all [subsetExponent_some, Finsupp.single_apply, eq_comm]
