-- Prove2me | solution 1 for CountingMatroid.Analysis.TwoLabelDerivativeNilpotence.two_label_derivative_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:56:32.765709+00:00
-- url     : https://prove2.me/submissions/d2d041fc-c035-44e9-bb6d-73f4fefb50eb

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Model_Prelude
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
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
namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
section


set_option autoImplicit false

/-! Squarefree label variables in the Tutte polynomial imply that three
derivatives in the sum of two label directions vanish. This uses no
operational rank or partition identification. -/

namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence

open CountingMatroid.Analysis.RankWeightQuadraticSignature
open scoped BigOperators

/-- INTERNAL: Partial derivatives commute, including repeated variables.
TEXLINE: main.tex:354-373 -/
theorem derivative_commute {α : Type} (x y : α) (p : MvPolynomial α ℚ) :
    MvPolynomial.pderiv x (MvPolynomial.pderiv y p) =
      MvPolynomial.pderiv y (MvPolynomial.pderiv x p) := by
  classical
  ext d
  simp only [MvPolynomial.coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h : x = y
  · subst y; rfl
  · simp [h, Ne.symm h, add_comm, add_left_comm]
    ring





/-- INTERNAL: A variable of degree at most one has vanishing second derivative.
TEXLINE: main.tex:334-339 -/
theorem squarefree_second_derivative {α : Type} (x : α) (p : MvPolynomial α ℚ)
    (hx : p.degreeOf x ≤ 1) :
    MvPolynomial.pderiv x (MvPolynomial.pderiv x p) = 0 := by
  classical
  ext d
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
  have hzero : p.coeff (d + Finsupp.single x 1 + Finsupp.single x 1) = 0 := by
    apply MvPolynomial.notMem_support_iff.mp
    apply MvPolynomial.notMem_support_of_degreeOf_lt x
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  simp [hzero]







end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence

end
set_option autoImplicit false

/-! Squarefree label variables in the Tutte polynomial imply that three
derivatives in the sum of two label directions vanish. This uses no
operational rank or partition identification. -/

namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TwoLabelDerivativeNilpotence

open CountingMatroid.Analysis.RankWeightQuadraticSignature
open scoped BigOperators

/-- INTERNAL: The third derivative in the sum of two squarefree label
directions vanishes by the pigeonhole principle.
TEXLINE: main.tex:412-417 -/
theorem solution {α : Type} (x y : α) (p : MvPolynomial α ℚ)
    (hx : p.degreeOf x ≤ 1) (hy : p.degreeOf y ≤ 1) :
    let D := fun g : MvPolynomial α ℚ => MvPolynomial.pderiv x g + MvPolynomial.pderiv y g
    D (D (D p)) = 0 := by
  dsimp only
  have hxx := squarefree_second_derivative x p hx
  have hyy := squarefree_second_derivative y p hy
  have hxyx : MvPolynomial.pderiv x (MvPolynomial.pderiv y (MvPolynomial.pderiv x p)) = 0 := by
    rw [derivative_commute x y, hxx, map_zero]
  have hxxy : MvPolynomial.pderiv x (MvPolynomial.pderiv x (MvPolynomial.pderiv y p)) = 0 := by
    rw [derivative_commute x y p, hxyx]
  have hyxy : MvPolynomial.pderiv y (MvPolynomial.pderiv x (MvPolynomial.pderiv y p)) = 0 := by
    rw [derivative_commute y x, hyy, map_zero]
  have hyyx : MvPolynomial.pderiv y (MvPolynomial.pderiv y (MvPolynomial.pderiv x p)) = 0 := by
    rw [derivative_commute y x p, hyxy]
  simp only [map_add, hxx, hyy, hxyx, hxxy, hyxy, hyyx, add_zero, zero_add]
