-- Prove2me | solution 1 for CountingMatroid.Analysis.SquarefreeFullDerivative.squarefree_fold_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:45:10.447985+00:00
-- url     : https://prove2.me/submissions/d07b8f2c-4e8a-436a-9df3-56b489cb3baf

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
set_option autoImplicit false

/-! Coefficient extraction for full coordinate derivatives of squarefree-label
homogenizations. The coefficient multiplier counts repeated homogenizer
coordinates while the label coordinates are distinct. -/

namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SquarefreeFullDerivative

open scoped BigOperators
open RankWeightSupportExchange

/-- INTERNAL: Extract a coefficient after distinct label derivatives and any
number of homogenizer derivatives. The queried coefficient has zero exponent
at each differentiated label. -/
theorem solution {α : Type} [DecidableEq α]
    (xs : List (Option α)) (p : MvPolynomial (Option α) ℚ)
    (m : Option α →₀ ℕ) (hnd : (xs.filterMap id).Nodup)
    (hm : ∀ a ∈ xs.filterMap id, m (some a) = 0) :
    (xs.foldr (fun s f => MvPolynomial.pderiv s f) p).coeff m =
      p.coeff (m + (Finsupp.single none (xs.count none) +
        ∑ a ∈ (xs.filterMap id).toFinset, Finsupp.single (some a) 1)) *
        ((m none + 1).ascFactorial (xs.count none) : ℚ) := by
  classical
  induction xs generalizing m with
  | nil => simp
  | cons s xs ih =>
    rw [List.foldr_cons, MvPolynomial.coeff_pderiv]
    cases s with
    | none =>
      have hm' : ∀ a ∈ xs.filterMap id, (m + Finsupp.single none 1 : Option α →₀ ℕ) (some a) = 0 := by
        simpa using hm
      rw [ih _ (by simpa using hnd) hm']
      have hexp : m + Finsupp.single none 1 +
          (Finsupp.single none (xs.count none) +
            ∑ a ∈ (xs.filterMap id).toFinset, Finsupp.single (some a) 1) =
          m + (Finsupp.single none ((none :: xs).count none) +
            ∑ a ∈ ((none :: xs).filterMap id).toFinset, Finsupp.single (some a) 1) := by
        simp only [List.count_cons_self, List.filterMap_cons, id_eq]
        rw [Finsupp.single_add]
        abel
      rw [hexp]
      simp only [List.count_cons_self, List.filterMap_cons, id_eq, Finsupp.add_apply,
        Finsupp.single_eq_same]
      have hf := Nat.succ_ascFactorial (m none + 1) (xs.count none)
      rw [← Nat.ascFactorial_succ] at hf
      have hfq := congrArg (fun n : ℕ => (n : ℚ)) hf
      push_cast at hfq
      simp only [Nat.succ_eq_add_one] at hfq
      calc
        _ = p.coeff _ * ((↑(m none) + 1) * ↑((m none + 1 + 1).ascFactorial (xs.count none))) := by ring
        _ = _ := by rw [hfq]
    | some a =>
      have hnd' : a ∉ xs.filterMap id ∧ (xs.filterMap id).Nodup := by simpa using hnd
      have hma : m (some a) = 0 := hm a (by simp)
      have hm' : ∀ b ∈ xs.filterMap id, (m + Finsupp.single (some a) 1 : Option α →₀ ℕ) (some b) = 0 := by
        intro b hb
        have hba : b ≠ a := by intro h; subst b; exact hnd'.1 hb
        simpa [Finsupp.single_apply, hba, Ne.symm hba] using hm b (by simpa only [List.filterMap_cons, id_eq] using List.mem_cons_of_mem a hb)
      rw [ih _ hnd'.2 hm']
      have hexp : m + Finsupp.single (some a) 1 +
          (Finsupp.single none (xs.count none) +
            ∑ b ∈ (xs.filterMap id).toFinset, Finsupp.single (some b) 1) =
          m + (Finsupp.single none (((some a) :: xs).count none) +
            ∑ b ∈ (((some a) :: xs).filterMap id).toFinset, Finsupp.single (some b) 1) := by
        simp only [List.count_cons_of_ne (Option.some_ne_none a), List.filterMap_cons, id_eq,
          List.toFinset_cons]
        rw [Finset.sum_insert (by simpa using hnd'.1)]
        abel
      rw [hexp]
      simp [hma]
