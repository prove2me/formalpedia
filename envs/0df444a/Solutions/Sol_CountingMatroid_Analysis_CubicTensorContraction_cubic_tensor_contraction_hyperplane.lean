-- Prove2me | solution 1 for CountingMatroid.Analysis.CubicTensorContraction.cubic_tensor_contraction_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:11:08.976174+00:00
-- url     : https://prove2.me/submissions/1326d168-96ae-4693-b541-522b06604828

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_CountingMatroid_Analysis_CubicExchangeCut_cubic_exchange_crosses_cut
import Theorems.Thm_CountingMatroid_Analysis_CubicTensorRayleighContraction_cubic_tensor_rayleigh_contraction
import Theorems.Thm_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane_HasNonpositiveHyperplane_nonpos_of_associated_eq_zero

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
section


set_option autoImplicit false

/-!
A quadratic form is nonpositive on a hyperplane if some real linear
functional has a nonpositive kernel. This property survives linear pullback
and nonnegative scaling. It implies the signature bound, and also gives
nonpositivity on the orthogonal complement of any positive vector.
No property of matroid polynomials is assumed or asserted here.
-/

namespace CountingMatroid.Analysis.QuadraticNonpositiveHyperplane





/-- INTERNAL: Nonnegative scaling preserves the same nonpositive hyperplane.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.smul {V : Type} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q)
    (c : ℝ) (hc : 0 ≤ c) : HasNonpositiveHyperplane (c • Q) := by
  obtain ⟨l, hl⟩ := hQ
  exact ⟨l, fun v hv => mul_nonpos_of_nonneg_of_nonpos hc (hl v hv)⟩





end CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

end
set_option autoImplicit false

/-!
The spectral part of cubic directional closure, stated independently of
polynomial calculus. A symmetric nonnegative tensor carries the exchange
support of a homogeneous cubic. The coordinate slices have at most one
positive direction; the remaining obligation is to propagate that bound to
every nonnegative contraction. Arbitrary sums of such slices have no such
closure property without the tensor and support hypotheses.

The remaining obligation is the degree-three instance of the nonnegative
directional-derivative closure cited in the paper. Brändén–Huh, Corollary
2.11, states this closure for the recursively defined classes of polynomials
with M-convex support and Lorentzian quadratic derivatives. The proof here
separates the proved exchange-to-connectivity argument from the analytic
Rayleigh contraction lemma, whose normalized spectral and boundary steps
remain open. The parent reduction does not assume an aggregate signature
bound or alter the theorem hypotheses.
-/

namespace CountingMatroid.Analysis.CubicTensorContraction
end CountingMatroid.Analysis.CubicTensorContraction
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicTensorContraction

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- PAPER: main.tex:340-347
BORROWED: Brändén–Huh, Lorentzian polynomials (2020), Corollary 2.11
(nonnegative directional derivatives), following Theorem 2.10.
The degree-three tensor formulation of the cited closure statement.
Symmetry, nonnegativity, and exchange support are essential compatibility
hypotheses; the statement does not assert closure of arbitrary sums.
For the cubic `(1 / 6) * ∑ s i j, T s i j * z s * z i * z j`,
the coordinate derivatives are one half of the displayed slice forms, and
the directional derivative is one half of their displayed weighted sum.
This normalization does not change a nonpositive-hyperplane witness.
The paper cites this closure rather than proving it. -/
theorem solution {σ : Type} [Fintype σ] [DecidableEq σ]
    (T : σ → σ → σ → ℚ) (hT : ∀ s i j, 0 ≤ T s i j)
    (hswap : ∀ s i j, T s i j = T i s j)
    (hlast : ∀ s i j, T s i j = T s j i)
    (hex : ∀ x ∈ cubicTensorSupport T, ∀ y ∈ cubicTensorSupport T,
      ∀ i, y i < x i → ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ cubicTensorSupport T)
    (hslice : ∀ s, HasNonpositiveHyperplane
      (Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))))
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    HasNonpositiveHyperplane (∑ s, (d s : ℝ) •
      Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))) := by
  classical
  by_cases hzero : ∀ s, d s = 0
  · refine ⟨0, ?_⟩
    intro v _
    simp [hzero]
  by_cases hsingle : ∃ a, ∀ s, s ≠ a → d s = 0
  · obtain ⟨a, ha⟩ := hsingle
    rw [Finset.sum_eq_single a]
    · exact (hslice a).smul (d a : ℝ) (by exact_mod_cast hd a)
    · intro s _ hsa
      simp [ha s hsa]
    · simp
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hreverse (s : σ) (e v : σ → ℝ)
      (he : 0 < Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) e) :
      Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) v *
        Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) e ≤
      ((Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))).associated e v) ^ 2 := by
    let Q := Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))
    change Q v * Q e ≤ (Q.associated e v) ^ 2
    have hv : Q.associated e ((Q e) • v - (Q.associated e v) • e) = 0 := by
      simp [QuadraticMap.associated_eq_self_apply, mul_comm]
    have hw := (hslice s).nonpos_of_associated_eq_zero e
      ((Q e) • v - (Q.associated e v) • e) he hv
    have hpolar : QuadraticMap.polar Q v e = 2 * Q.associated e v := by
      have h := congrArg (fun B : LinearMap.BilinForm ℝ (σ → ℝ) => B v e)
        (QuadraticMap.two_nsmul_associated ℝ Q)
      simpa only [LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.associated_isSymm ℝ Q v e]
        using h.symm
    have hexp : Q ((Q e) • v - (Q.associated e v) • e) =
        Q e * (Q v * Q e - (Q.associated e v) ^ 2) := by
      rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpolar]
      simp only [QuadraticMap.map_smul, smul_eq_mul]
      ring
    change Q ((Q e) • v - (Q.associated e v) • e) ≤ 0 at hw
    rw [hexp] at hw
    have hprod : Q v * Q e - (Q.associated e v) ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ he).mp (by simpa using hw)
    linarith
  have hcross (U : Set σ)
      (hin : ∃ s i j, T s i j ≠ 0 ∧ s ∈ U)
      (hout : ∃ s i j, T s i j ≠ 0 ∧ s ∉ U) :
      ∃ s i j, T s i j ≠ 0 ∧ i ∈ U ∧ j ∉ U := by
    exact CubicExchangeCut.cubic_exchange_crosses_cut T hswap hlast
      (cubicTensorSupport T) (fun _ => Iff.rfl) hex U hin hout
  exact CubicTensorRayleighContraction.cubic_tensor_rayleigh_contraction
    T hT hswap hlast hcross hreverse d hd
