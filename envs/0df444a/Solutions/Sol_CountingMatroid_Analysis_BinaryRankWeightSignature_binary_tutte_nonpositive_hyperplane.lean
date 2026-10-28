-- Prove2me | solution 1 for CountingMatroid.Analysis.BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:27:52.701717+00:00
-- url     : https://prove2.me/submissions/38bb833c-3fa7-4268-a44f-e32348671633

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Theorems.Thm_CountingMatroid_Analysis_BinaryRankWeightSignature_binary_form_nonpositive_hyperplane
import Theorems.Thm_CountingMatroid_Analysis_BinaryRankWeightSignature_rank_weight_pair_le

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

/-- INTERNAL: The original-variable quadratic signature invariant is proved
for every matroid on two elements, directly from rank submodularity.
TEXLINE: main.tex:334-348 -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (htwo : Fintype.card α = 2) :
    let p : MvPolynomial (Option α) ℚ := ∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)
    HasNonpositiveHyperplane (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j p)) : ℚ) : ℝ))) := by
  classical
  dsimp only
  obtain ⟨s, t, hst, hu⟩ := Finset.card_eq_two.mp
    (show (Finset.univ : Finset α).card = 2 by simpa)
  let b : ℚ := (q ^ (N.eRk ({s} : Set α)).toNat)⁻¹
  let c : ℚ := (q ^ (N.eRk ({t} : Set α)).toNat)⁻¹
  let d : ℚ := (q ^ (N.eRk ({s,t} : Set α)).toNat)⁻¹
  have hsets : (Finset.univ : Finset (Finset α)) = {∅, {s}, {t}, {s,t}} := by
    rw [← Finset.powerset_univ, hu]
    simp [Finset.powerset_insert]
    ext A
    simp [or_left_comm, or_assoc, eq_comm]
  have hstsets : ({s} : Finset α) ≠ {t} := by simpa using hst
  have hs_pair : ({s} : Finset α) ≠ {s,t} := by
    intro h
    have ht : t ∈ ({s} : Finset α) := h.symm ▸ (by simp)
    exact hst (Finset.mem_singleton.mp ht).symm
  have ht_pair : ({t} : Finset α) ≠ {s,t} := by
    intro h
    have hs : s ∈ ({t} : Finset α) := h.symm ▸ (by simp)
    exact hst (Finset.mem_singleton.mp hs)
  have hempair : (∅ : Finset α) ≠ {s,t} := by
    intro h
    have hs : s ∈ (∅ : Finset α) := h.symm ▸ (by simp)
    simp at hs
  have hT : (∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a) : MvPolynomial (Option α) ℚ) =
      MvPolynomial.X none ^ 2 +
        MvPolynomial.C b * MvPolynomial.X none * MvPolynomial.X (some s) +
        MvPolynomial.C c * MvPolynomial.X none * MvPolynomial.X (some t) +
        MvPolynomial.C d * MvPolynomial.X (some s) * MvPolynomial.X (some t) := by
    rw [hsets]
    rw [Finset.sum_insert (by simp [hempair]),
      Finset.sum_insert (by simp [hstsets, hs_pair]),
      Finset.sum_insert (by simp [ht_pair]), Finset.sum_singleton]
    simp [htwo, hst, Finset.prod_insert, b, c, d]
    ring
  rw [hT]
  have hoption : (Finset.univ : Finset (Option α)) = {none, some s, some t} := by
    ext x
    cases x with
    | none => simp
    | some x =>
      have hx : x ∈ ({s,t} : Finset α) := hu ▸ Finset.mem_univ x
      simpa using hx
  let H : Matrix (Option α) (Option α) ℝ := fun i j => ((MvPolynomial.constantCoeff
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j
          (MvPolynomial.X none ^ 2 +
            MvPolynomial.C b * MvPolynomial.X none * MvPolynomial.X (some s) +
            MvPolynomial.C c * MvPolynomial.X none * MvPolynomial.X (some t) +
            MvPolynomial.C d * MvPolynomial.X (some s) * MvPolynomial.X (some t)))) : ℚ) : ℝ)
  have htwoCoeff : MvPolynomial.constantCoeff (2 : MvPolynomial (Option α) ℚ) = 2 :=
    map_ofNat _ _
  have hform : H.toQuadraticForm' =
      (2 : ℝ) • QuadraticMap.linMulLin (LinearMap.proj none) (LinearMap.proj none) +
        (2 * (b : ℝ)) • QuadraticMap.linMulLin (LinearMap.proj none) (LinearMap.proj (some s)) +
        (2 * (c : ℝ)) • QuadraticMap.linMulLin (LinearMap.proj none) (LinearMap.proj (some t)) +
        (2 * (d : ℝ)) • QuadraticMap.linMulLin (LinearMap.proj (some s)) (LinearMap.proj (some t)) := by
    ext v
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply]
    rw [hoption]
    simp [H, MvPolynomial.pderiv_X, Pi.single_apply, hst, hst.symm,
      QuadraticMap.linMulLin_apply, htwoCoeff]
    ring
  change HasNonpositiveHyperplane H.toQuadraticForm'
  rw [hform]
  apply binary_form_nonpositive_hyperplane
  · exact_mod_cast inv_pos.mpr (pow_pos hq _)
  · exact_mod_cast inv_pos.mpr (pow_pos hq _)
  · exact_mod_cast (inv_pos.mpr (pow_pos hq _)).le
  · exact_mod_cast rank_weight_pair_le N q hq hqone s t
