-- Prove2me | solution 1 for CountingMatroid.Analysis.BinaryRankWeightSignature.rank_weight_pair_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:45:00.10364+00:00
-- url     : https://prove2.me/submissions/547a9218-0fa0-45c7-8b84-8b9fe293926d

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
set_option autoImplicit false

/-!
The two-element rank-weight signature calculation. Submodularity bounds the
pair coefficient by the product of the singleton coefficients. The resulting
quadratic has a nonpositive hyperplane, as seen by completing two squares.
-/

namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BinaryRankWeightSignature

open QuadraticNonpositiveHyperplane
open scoped BigOperators

/-- INTERNAL: Matroid rank submodularity gives the precise coefficient
inequality used in the two-element quadratic calculation.
TEXLINE: main.tex:334-348 -/
theorem solution {α : Type} [Finite α] (N : Matroid α)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1) (s t : α) :
    (q ^ (N.eRk ({s, t} : Set α)).toNat)⁻¹ ≤
      (q ^ (N.eRk ({s} : Set α)).toNat)⁻¹ *
        (q ^ (N.eRk ({t} : Set α)).toNat)⁻¹ := by
  have hr := N.eRk_union_le_eRk_add_eRk ({s} : Set α) ({t} : Set α)
  have hs := (N.isRkFinite_set ({s} : Set α)).eRk_lt_top.ne
  have ht := (N.isRkFinite_set ({t} : Set α)).eRk_lt_top.ne
  have hn := ENat.toNat_le_toNat hr (by simp [hs, ht])
  rw [ENat.toNat_add hs ht] at hn
  have hp : q ^ ((N.eRk ({s} : Set α)).toNat + (N.eRk ({t} : Set α)).toNat) ≤
      q ^ (N.eRk ({s, t} : Set α)).toNat := by
    apply pow_le_pow_of_le_one hq.le hqone
    simpa only [Set.singleton_union] using hn
  rw [← mul_inv_rev, ← pow_add]
  exact (inv_le_inv₀ (pow_pos hq _) (pow_pos hq _)).mpr (by simpa only [Nat.add_comm] using hp)
