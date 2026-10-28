-- Prove2me | solution 1 for CountingMatroid.Analysis.SquarefreeCoordinateHessian.squarefree_coordinate_hessian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:53:10.527988+00:00
-- url     : https://prove2.me/submissions/7007b4b0-2455-46a8-bd1f-84026b13572d

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
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
import Theorems.Thm_CountingMatroid_Analysis_SquarefreeCoordinateHessian_squarefree_fold_zero_of_not_nodup
import Theorems.Thm_CountingMatroid_Analysis_SquarefreeFullDerivative_squarefree_full_derivative

namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
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

/-! Coordinate differentiation of a homogeneous polynomial whose label
variables are squarefree reduces its constant Hessian to a residual matrix.
The matrix records the selected labels and the number of homogenizer
derivatives. This calculation concerns arbitrary subset coefficients and
does not assume a matroid signature bound. -/

namespace CountingMatroid.Analysis.SquarefreeCoordinateHessian

open scoped BigOperators
open LorentzianDirectionalSignature



/-- INTERNAL: Separate homogenizer derivatives from the list of label
derivatives without losing multiplicity. -/
theorem option_list_length {α : Type} [DecidableEq α] (xs : List (Option α)) :
    xs.count none + (xs.filterMap id).length = xs.length := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
    cases s <;> simp at * <;> omega









end CountingMatroid.Analysis.SquarefreeCoordinateHessian

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed the coordinate Hessian identity using the full-derivative coefficient formula; all four entries have the common homogenizer factorial, and repeated labels give zero.

* 2026-10-09 · partial · after live handoff deferral, proved coordinate-fold commutation and monomial annihilation when a derivative count exceeds its exponent. This closes the normal form for repeated labels anywhere in the list. Only the distinct-label factorial coefficient identity remains open.
* 2026-10-09 · decomposed · defined the exact residual Hessian and proved the derivative-list cardinality identity; instantiated the distinct-label witnesses and reduced the normal form to monomial coefficient extraction. Repeated-label annihilation remains part of the same polynomial obligation.
-/

end
set_option autoImplicit false

/-! Coordinate differentiation of a homogeneous polynomial whose label
variables are squarefree reduces its constant Hessian to a residual matrix.
The matrix records the selected labels and the number of homogenizer
derivatives. This calculation concerns arbitrary subset coefficients and
does not assume a matroid signature bound. -/

namespace CountingMatroid.Analysis.SquarefreeCoordinateHessian
end CountingMatroid.Analysis.SquarefreeCoordinateHessian
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SquarefreeCoordinateHessian

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: Every quadratic coordinate descendant of a squarefree-label
homogenization is a nonnegative scalar multiple of its explicit residual
Hessian. Repeated label derivatives give the zero scalar. For distinct labels
the witnesses are their set, the count of `none`, and that count's factorial.
This identity holds for arbitrary rational subset coefficients.
TEXLINE: main.tex:334-348 -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (xs : List (Option α))
    (hlength : xs.length + 2 = Fintype.card α) :
    ∃ (S : Finset α) (k : ℕ) (c : ℝ),
      0 ≤ c ∧ S.card + k + 2 = Fintype.card α ∧
      constantHessianForm
        (xs.foldr (fun s f => MvPolynomial.pderiv s f)
          (∑ A : Finset α,
            MvPolynomial.C (w A) *
              MvPolynomial.X none ^ (Fintype.card α - A.card) *
                ∏ a ∈ A, MvPolynomial.X (some a))) =
        c • (squarefreeResidualHessian w S k).toQuadraticForm' := by
  classical
  by_cases hnd : (xs.filterMap id).Nodup
  · refine ⟨(xs.filterMap id).toFinset, xs.count none,
      (Nat.factorial (xs.count none) : ℝ), by positivity, ?_, ?_⟩
    · rw [List.toFinset_card_of_nodup hnd]
      have hlen := option_list_length xs
      omega
    · have hfull (i j : Option α) (hn : ((i :: j :: xs).filterMap id).Nodup) :
          MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
            (xs.foldr (fun s f => MvPolynomial.pderiv s f)
              (∑ A : Finset α, MvPolynomial.C (w A) *
                MvPolynomial.X none ^ (Fintype.card α - A.card) *
                  ∏ a ∈ A, MvPolynomial.X (some a))))) =
          w ((i :: j :: xs).filterMap id).toFinset *
            (Nat.factorial ((i :: j :: xs).count none) : ℚ) := by
        exact SquarefreeFullDerivative.squarefree_full_derivative w (i :: j :: xs) hn
          (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength)
      have hzero (i j : Option α) (hn : ¬ ((i :: j :: xs).filterMap id).Nodup) :
          MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
            (xs.foldr (fun s f => MvPolynomial.pderiv s f)
              (∑ A : Finset α, MvPolynomial.C (w A) *
                MvPolynomial.X none ^ (Fintype.card α - A.card) *
                  ∏ a ∈ A, MvPolynomial.X (some a))))) = 0 := by
        change MvPolynomial.constantCoeff ((i :: j :: xs).foldr _ _) = 0
        rw [squarefree_fold_zero_of_not_nodup w (i :: j :: xs) hn, map_zero]
      have hentry (i j : Option α) :
          ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
            (xs.foldr (fun s f => MvPolynomial.pderiv s f)
              (∑ A : Finset α, MvPolynomial.C (w A) *
                MvPolynomial.X none ^ (Fintype.card α - A.card) *
                  ∏ a ∈ A, MvPolynomial.X (some a))))) : ℚ) : ℝ) =
          (Nat.factorial (xs.count none) : ℝ) *
            squarefreeResidualHessian w (xs.filterMap id).toFinset (xs.count none) i j := by
        cases i with
        | none =>
          cases j with
          | none =>
            rw [hfull none none (by simpa using hnd)]
            simp [squarefreeResidualHessian, Nat.factorial_succ]
            ring
          | some a =>
            by_cases ha : some a ∈ xs
            · rw [hzero none (some a) (by simp [ha])]
              simp [squarefreeResidualHessian, ha]
            · rw [hfull none (some a) (by simpa [ha] using hnd)]
              simp [squarefreeResidualHessian, ha, Nat.factorial_succ]
              ring
        | some a =>
          cases j with
          | none =>
            by_cases ha : some a ∈ xs
            · rw [hzero (some a) none (by simp [ha])]
              simp [squarefreeResidualHessian, ha]
            · rw [hfull (some a) none (by simpa [ha] using hnd)]
              simp [squarefreeResidualHessian, ha, Nat.factorial_succ]
              ring
          | some b =>
            by_cases hab : some a ∈ xs ∨ some b ∈ xs ∨ a = b
            · rw [hzero (some a) (some b) (by
                simp only [List.filterMap_cons, id_eq, List.nodup_cons, List.mem_cons]
                simp only [List.mem_filterMap, exists_eq_right] at *
                tauto)]
              simp [squarefreeResidualHessian, hab]
            · have ha : some a ∉ xs := fun h => hab (Or.inl h)
              have hb : some b ∉ xs := fun h => hab (Or.inr (Or.inl h))
              have he : a ≠ b := fun h => hab (Or.inr (Or.inr h))
              rw [hfull (some a) (some b) (by simpa [List.nodup_cons, ha, hb, he] using hnd)]
              simp [squarefreeResidualHessian, ha, hb, he]
              ring
      unfold constantHessianForm
      have hmatrix : (fun i j =>
          ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
            (xs.foldr (fun s f => MvPolynomial.pderiv s f)
              (∑ A : Finset α, MvPolynomial.C (w A) *
                MvPolynomial.X none ^ (Fintype.card α - A.card) *
                  ∏ a ∈ A, MvPolynomial.X (some a))))) : ℚ) : ℝ)) =
          (Nat.factorial (xs.count none) : ℝ) •
            squarefreeResidualHessian w (xs.filterMap id).toFinset (xs.count none) := by
        ext i j
        exact hentry i j
      rw [hmatrix]
      simp only [Matrix.toQuadraticForm', map_smul,
        LinearMap.BilinMap.toQuadraticMap_smul]
      rfl
  · refine ⟨∅, Fintype.card α - 2, 0, le_rfl, ?_, ?_⟩
    · simp only [Finset.card_empty]
      omega
    · rw [zero_smul]
      have hpzero := squarefree_fold_zero_of_not_nodup w xs hnd
      rw [hpzero]
      ext v
      simp only [constantHessianForm, map_zero, Rat.cast_zero,
        Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
        QuadraticMap.zero_apply]
      change Matrix.toLinearMap₂' ℝ (0 : Matrix (Option α) (Option α) ℝ) v v = 0
      rw [map_zero]
      rfl
