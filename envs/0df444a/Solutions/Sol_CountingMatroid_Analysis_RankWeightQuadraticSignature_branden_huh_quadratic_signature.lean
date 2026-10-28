-- Prove2me | solution 1 for CountingMatroid.Analysis.RankWeightQuadraticSignature.branden_huh_quadratic_signature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:17:26.282754+00:00
-- url     : https://prove2.me/submissions/4c6b7c65-8e0c-4463-97b6-41fd85ae360e

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
import Theorems.Thm_CountingMatroid_Analysis_BinaryRankWeightSignature_binary_tutte_nonpositive_hyperplane
import Theorems.Thm_CountingMatroid_Analysis_LinearSubstitutionHessian_linear_aeval_hessian_quadraticForm
import Theorems.Thm_CountingMatroid_Analysis_MixedDirectionalRankWeightSignature_mixed_directional_rank_weight_nonpositive_hyperplane
import Theorems.Thm_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane_HasNonpositiveHyperplane_nonpos_of_associated_eq_zero
import Theorems.Thm_CountingMatroid_Analysis_RankWeightQuadraticSignature_descendant_constant
import Theorems.Thm_CountingMatroid_Analysis_RankWeightQuadraticSignature_descendant_directional_normal_form
import Theorems.Thm_CountingMatroid_Analysis_RankWeightQuadraticSignature_descendant_homogeneous_degree_le
import Theorems.Thm_CountingMatroid_Analysis_RankWeightQuadraticSignature_tuttePolynomial_isHomogeneous
import Theorems.Thm_CountingMatroid_Analysis_RankWeightQuadraticSignature_tutte_descendant_coeff_nonneg

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

/-!
A quadratic form is nonpositive on a hyperplane if some real linear
functional has a nonpositive kernel. This property survives linear pullback
and nonnegative scaling. It implies the signature bound, and also gives
nonpositivity on the orthogonal complement of any positive vector.
No property of matroid polynomials is assumed or asserted here.
-/

namespace CountingMatroid.Analysis.QuadraticNonpositiveHyperplane



/-- INTERNAL: Pulling back a nonpositive hyperplane needs no injectivity,
surjectivity, or sign conditions on the linear map.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.comp {V W : Type}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q) (A : W →ₗ[ℝ] V) :
    HasNonpositiveHyperplane (Q.comp A) := by
  obtain ⟨l, hl⟩ := hQ
  exact ⟨l.comp A, fun v hv => hl (A v) hv⟩

/-- INTERNAL: Nonnegative scaling preserves the same nonpositive hyperplane.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.smul {V : Type} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q)
    (c : ℝ) (hc : 0 ≤ c) : HasNonpositiveHyperplane (c • Q) := by
  obtain ⟨l, hl⟩ := hQ
  exact ⟨l, fun v hv => mul_nonpos_of_nonneg_of_nonpos hc (hl v hv)⟩

/-- INTERNAL: Rank-nullity converts the hyperplane witness to the exact
positive-signature bound used for quadratic descendants.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.sigPos_le_one {V : Type}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q) : sigPos Q ≤ 1 := by
  obtain ⟨l, hl⟩ := hQ
  have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (V := LinearMap.ker l) (fun v hv => hl v (LinearMap.mem_ker.mp hv))
  have hnull := l.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (LinearMap.range l) ≤ 1 := by
    simpa using (LinearMap.range l).finrank_le
  omega



end CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

end

section


set_option autoImplicit false

/-!
The precise external signature input, separate from the operational rank
correspondence and coefficient extraction proved in the counting paper.
`Descendant` records only partial derivatives, nonnegative linear
substitutions, and nonnegative scalar multiplication. The signature uses
Mathlib's maximum dimension of a positive definite subspace over the reals.
The empty- and singleton-ground signature cases are proved, using the
homogeneous-degree invariant of every descendant. The two-element ground
case is proved by rank submodularity and a two-square calculation, with
the resulting hyperplane transported through every allowed substitution.
The signature case with at most one output variable follows from the ambient
dimension bound. The remaining
Bränden–Huh input is the unresolved borrowed mixed-derivative prerequisite
in `MixedDirectionalRankWeightSignature`. The exact normal
form of a descendant is proved: nonnegative directional derivatives in the
original variables, followed by one nonnegative linear substitution and a
nonnegative scalar. A nonzero quadratic uses exactly ground-set size minus
two derivatives. The unresolved signature bound is applied to this normal
form. A proved nonpositive-hyperplane invariant transports the Hessian
through the final substitution and scaling and recovers the exact orthogonal
kernel used by the signature bound. Only its establishment for the original
mixed directional derivative on ground sets of size at least three remains
open in that support module; no Lorentzian assumption has been introduced.
-/

namespace CountingMatroid.Analysis.RankWeightQuadraticSignature

open scoped BigOperators









/-- INTERNAL: Compute a Hessian entry directly from a degree-two coefficient;
the repeated-variable coefficient has multiplicity two.
TEXLINE: main.tex:408-417 -/
theorem hessian_coefficient {τ : Type} [DecidableEq τ]
    (g : MvPolynomial τ ℚ) (s t : τ) :
    hessian g s t =
      ((g.coeff (Finsupp.single s 1 + Finsupp.single t 1) *
        (if s = t then 2 else 1) : ℚ) : ℝ) := by
  classical
  unfold hessian
  rw [MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_pderiv]
  by_cases h : s = t
  · subst t
    norm_num
  · simp [h, Finsupp.single_apply, Ne.symm h]





/-- INTERNAL: Linear substitution preserves homogeneous degree, including
zero columns and identification of variables.
TEXLINE: main.tex:326-343 -/
theorem linearSubstitution_isHomogeneous {σ τ : Type} [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) (d : ℕ)
    (hp : p.IsHomogeneous d) : (linearSubstitution a p).IsHomogeneous d := by
  unfold linearSubstitution
  simpa only [one_mul] using hp.aeval
    (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t)
    (fun s => MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
      (fun t _ => MvPolynomial.isHomogeneous_C_mul_X (a s t) t))











/-- INTERNAL: The degree of an iterated directional derivative decreases
by the number of directions, with truncated subtraction covering zero.
TEXLINE: main.tex:334-348 -/
theorem iteratedDirectionalDerivative_isHomogeneous {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (d : ℕ) (hp : p.IsHomogeneous d)
    (ds : List (σ → ℚ)) :
    (iteratedDirectionalDerivative ds p).IsHomogeneous (d - ds.length) := by
  induction ds with
  | nil => simpa [iteratedDirectionalDerivative] using hp
  | cons a ds ih =>
    have h := MvPolynomial.IsHomogeneous.sum Finset.univ
      (fun s => MvPolynomial.C (a s) *
        MvPolynomial.pderiv s (iteratedDirectionalDerivative ds p))
      (d - ds.length - 1) (fun s _ => ih.pderiv.C_mul (a s))
    simpa [iteratedDirectionalDerivative, Nat.sub_sub] using h

/-- INTERNAL: Identify the parent's directional-derivative recursion with
the library-list fold used by the independent mixed-derivative prerequisite.
TEXLINE: main.tex:334-348 -/
theorem iteratedDirectionalDerivative_eq_foldr {σ : Type} [Fintype σ]
    (ds : List (σ → ℚ)) (p : MvPolynomial σ ℚ) :
    iteratedDirectionalDerivative ds p =
      ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [iteratedDirectionalDerivative, List.foldr_cons, ih]

/-- INTERNAL: Scalar multiplication of a rational polynomial scales its
real Hessian quadratic form by the same scalar.
TEXLINE: main.tex:326-348 -/
theorem hessian_C_mul {τ : Type} [Fintype τ] [DecidableEq τ]
    (c : ℚ) (p : MvPolynomial τ ℚ) :
    (hessian (MvPolynomial.C c * p)).toQuadraticForm' =
      (c : ℝ) • (hessian p).toQuadraticForm' := by
  have hmat : hessian (MvPolynomial.C c * p) = (c : ℝ) • hessian p := by
    ext i j
    simp [hessian]
  rw [hmat]
  unfold Matrix.toQuadraticForm'
  rw [map_smul, LinearMap.BilinMap.toQuadraticMap_smul]

/-- INTERNAL: Linear substitution of a rational polynomial pulls back its
real Hessian quadratic form, including singular substitutions.
TEXLINE: main.tex:326-348 -/
theorem hessian_linearSubstitution {σ τ : Type} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) :
    (hessian (linearSubstitution a p)).toQuadraticForm' =
      (hessian p).toQuadraticForm'.comp (Matrix.toLin' (fun s t => (a s t : ℝ))) := by
  exact LinearSubstitutionHessian.linear_aeval_hessian_quadraticForm a p



end CountingMatroid.Analysis.RankWeightQuadraticSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · handoff-ready · after the live scheduler opened capacity, isolated the sole remaining original-variable invariant in MixedDirectionalRankWeightSignature and proved the fold identity connecting it to the parent. All other children are proved; the parent uses the independent prerequisite and contains no remaining proof hole of its own. The prerequisite still has the mixed-directional compatibility gap, so this is a proof boundary, not a completed Bränden–Huh proof.
* 2026-10-09 · partial · proved Hessian congruence under linear substitution and scalar scaling, and the nonpositive-hyperplane invariant with its pullback, scaling, signature and positive-vector orthogonal-kernel consequences. Proved the two-element Tutte quadratic by the exact rank-weight pair bound and a two-square identity, so the parent closes every descendant on ground sets of size at most two. Its single remaining gap is establishment of the invariant for |α|≥3 after exactly |α|-2 nonnegative directional derivatives; all subsequent transport is proved. No new assumption or open child was introduced.
* 2026-10-09 · partial · proved the linear polynomial chain rule and substitution composition in LinearPolynomialChainRule, then proved finite intermediate variables, the exact directional normal form, and its homogeneous degree. The parent uses this representation and proves that its direction list has length |α|-2 and its scalar is positive. The original nonpositive-kernel gap now concerns this normalized expression. A stdin application of eRk_submod failed by statement shape; separate checked stdin examples show that adding two signature-one forms can produce signature two. The unresolved cited input is compatibility of mixed nonnegative directional derivatives of the common matroid polynomial, not the algebraic normalization. No assumption or new open helper was introduced.
* 2026-10-09 · partial · proved the at-most-one-output-variable branch using sigPos_le_finrank and Module.finrank_pi; preserved all earlier homogeneous-degree, coefficient-cone and small-ground proofs. Current statement-shape searches found no matroid-polynomial, Lorentzian closure or substitute spectral declaration supplying nonpositivity on the positive-vector orthogonal complement. The remaining cited Bränden–Huh input stays open in its original theorem, without new helpers or assumptions.
* 2026-10-09 · blocked · preserved the proved empty-ground branch; searched project, pinned Mathlib and Arlib for Lorentzian rank-weight base, closure and quadratic signature results without finding an applicable declaration. A stdin application of descendant_constant to the nonempty branch fails because its initial polynomial must be constant. Proposed the unchanged cited Bränden–Huh consequence as prior input; introduced no helper or assumption.
-/

end
set_option autoImplicit false

/-!
The precise external signature input, separate from the operational rank
correspondence and coefficient extraction proved in the counting paper.
`Descendant` records only partial derivatives, nonnegative linear
substitutions, and nonnegative scalar multiplication. The signature uses
Mathlib's maximum dimension of a positive definite subspace over the reals.
The empty- and singleton-ground signature cases are proved, using the
homogeneous-degree invariant of every descendant. The two-element ground
case is proved by rank submodularity and a two-square calculation, with
the resulting hyperplane transported through every allowed substitution.
The signature case with at most one output variable follows from the ambient
dimension bound. The remaining
Bränden–Huh input is the unresolved borrowed mixed-derivative prerequisite
in `MixedDirectionalRankWeightSignature`. The exact normal
form of a descendant is proved: nonnegative directional derivatives in the
original variables, followed by one nonnegative linear substitution and a
nonnegative scalar. A nonzero quadratic uses exactly ground-set size minus
two derivatives. The unresolved signature bound is applied to this normal
form. A proved nonpositive-hyperplane invariant transports the Hessian
through the final substitution and scaling and recovers the exact orthogonal
kernel used by the signature bound. Only its establishment for the original
mixed directional derivative on ground sets of size at least three remains
open in that support module; no Lorentzian assumption has been introduced.
-/

namespace CountingMatroid.Analysis.RankWeightQuadraticSignature
end CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightQuadraticSignature

open scoped BigOperators

/-- PAPER: main.tex:334-348
BORROWED: Bränden–Huh, Lorentzian polynomials (2020), Theorems 4.10,
2.10 and Corollary 2.11, together with the defining quadratic signature.
Only their quadratic consequence is required, after a finite sequence of
the cited closure operations. This does not assert any operational rank
identity or identify any partition coefficient. -/
theorem solution {α τ : Type} [Fintype α] [Fintype τ]
    [DecidableEq τ] (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1) (g : MvPolynomial τ ℚ)
    (hg : Descendant (tuttePolynomial N q) τ g)
    (hdegree : g.IsHomogeneous 2) :
    sigPos (hessian g).toQuadraticForm' ≤ 1 := by
  classical
  by_cases hτsmall : Fintype.card τ ≤ 1
  · have hd := sigPos_le_finrank (hessian g).toQuadraticForm'
    rw [Module.finrank_pi] at hd
    exact hd.trans hτsmall
  by_cases hempty : Fintype.card α = 0
  · haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hempty
    have hU : (Finset.univ : Finset (Finset α)) = {∅} := by
      ext A
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim A ∅
    have hT : tuttePolynomial N q = MvPolynomial.C 1 := by
      unfold tuttePolynomial
      rw [hU, Finset.sum_singleton]
      simp only [Finset.coe_empty, Matroid.eRk_empty, ENat.toNat_zero,
        pow_zero, inv_one, Finset.card_empty, Nat.sub_zero, hempty,
        Finset.prod_empty, mul_one]
    rw [hT] at hg
    obtain ⟨c, rfl⟩ := descendant_constant 1 g hg
    have hz : hessian (MvPolynomial.C c : MvPolynomial τ ℚ) = 0 := by
      ext s t
      simp [hessian]
    rw [hz]
    have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
      (Q := (0 : Matrix τ τ ℝ).toQuadraticForm') (V := ⊤)
      (by intro v hv; simp [Matrix.toQuadraticForm'])
    have htop : Module.finrank ℝ (⊤ : Submodule ℝ (τ → ℝ)) =
        Module.finrank ℝ (τ → ℝ) := by simp
    rw [htop] at hdim
    omega
  ·
    obtain ⟨k, hk, hhom⟩ := descendant_homogeneous_degree_le
      (tuttePolynomial N q) g (Fintype.card α)
      (tuttePolynomial_isHomogeneous N q) hg
    by_cases hsmall : Fintype.card α < 2
    · have hgzero : g = 0 := by
        by_contra hne
        have heq := hhom.inj_right hdegree hne
        omega
      rw [hgzero]
      have hz : hessian (0 : MvPolynomial τ ℚ) = 0 := by
        ext s t
        simp [hessian]
      rw [hz]
      have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
        (Q := (0 : Matrix τ τ ℝ).toQuadraticForm') (V := ⊤)
        (by intro v hv; simp [Matrix.toQuadraticForm'])
      have htop : Module.finrank ℝ (⊤ : Submodule ℝ (τ → ℝ)) =
          Module.finrank ℝ (τ → ℝ) := by simp
      rw [htop] at hdim
      omega
    · have hcoeff := tutte_descendant_coeff_nonneg N q hq g hg
      have hentry (s t : τ) : 0 ≤ hessian g s t := by
        rw [hessian_coefficient]
        exact_mod_cast mul_nonneg (hcoeff _)
          (show (0 : ℚ) ≤ if s = t then 2 else 1 by split_ifs <;> norm_num)
      by_cases hpositive : ∃ s t, 0 < hessian g s t
      · let Q := (hessian g).toQuadraticForm'
        let e : τ → ℝ := fun _ => 1
        have hQe : 0 < Q e := by
          obtain ⟨s, t, hst⟩ := hpositive
          have hrow : 0 < ∑ t, hessian g s t :=
            Finset.sum_pos' (fun t _ => hentry s t)
              ⟨t, Finset.mem_univ t, hst⟩
          have hsum : 0 < ∑ s, ∑ t, hessian g s t :=
            Finset.sum_pos' (fun s _ => Finset.sum_nonneg (fun t _ => hentry s t))
              ⟨s, Finset.mem_univ s, hrow⟩
          simpa [Q, e, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply] using hsum
        letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
        let l : (τ → ℝ) →ₗ[ℝ] ℝ := Q.associated e
        suffices hnonpos : ∀ v ∈ LinearMap.ker l, Q v ≤ 0 by
          exact QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane.sigPos_le_one
            ⟨l, fun v hv => hnonpos v (LinearMap.mem_ker.mpr hv)⟩
        have hgne : g ≠ 0 := by
          intro hgzero
          have hz : hessian g = 0 := by
            rw [hgzero]
            ext s t
            simp [hessian]
          have hzero : Q e = 0 := by
            simp [Q, hz, Matrix.toQuadraticForm']
          linarith
        obtain ⟨c, a, ds, hc, ha, hds, hrepr⟩ :=
          descendant_directional_normal_form (tuttePolynomial N q) g hg
        have hnormaldegree : g.IsHomogeneous (Fintype.card α - ds.length) := by
          rw [hrepr]
          exact (linearSubstitution_isHomogeneous a _ _
            (iteratedDirectionalDerivative_isHomogeneous _ _
              (tuttePolynomial_isHomogeneous N q) ds)).C_mul c
        have hlength : ds.length + 2 = Fintype.card α := by
          have heq := hnormaldegree.inj_right hdegree hgne
          omega
        have hcpos : 0 < c := by
          have hcne : c ≠ 0 := by
            intro hc0
            apply hgne
            simp [hrepr, hc0]
          exact lt_of_le_of_ne hc hcne.symm
        have hsource : QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane
            (hessian (iteratedDirectionalDerivative ds (tuttePolynomial N q))).toQuadraticForm' := by
          by_cases htwo : Fintype.card α = 2
          · have hdszero : ds = [] := List.length_eq_zero_iff.mp (by omega)
            rw [hdszero]
            dsimp only [iteratedDirectionalDerivative]
            exact BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
              N q hq hqone htwo
          · rw [iteratedDirectionalDerivative_eq_foldr]
            exact MixedDirectionalRankWeightSignature.mixed_directional_rank_weight_nonpositive_hyperplane
              N hfull q hq hqone ds hds hlength
        have htransform : Q = (c : ℝ) •
            (hessian (iteratedDirectionalDerivative ds (tuttePolynomial N q))).toQuadraticForm'.comp
              (Matrix.toLin' (fun s t => (a s t : ℝ))) := by
          dsimp only [Q]
          rw [hrepr, hessian_C_mul, hessian_linearSubstitution]
        have hwhole : QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane Q := by
          rw [htransform]
          exact (hsource.comp _).smul c (by exact_mod_cast hc)
        intro v hv
        exact hwhole.nonpos_of_associated_eq_zero e v hQe (LinearMap.mem_ker.mp hv)

      · have hz : hessian g = 0 := by
          ext s t
          have hnot : ¬ 0 < hessian g s t := fun hst => hpositive ⟨s, t, hst⟩
          exact le_antisymm (le_of_not_gt hnot) (hentry s t)
        rw [hz]
        have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
          (Q := (0 : Matrix τ τ ℝ).toQuadraticForm') (V := ⊤)
          (by intro v hv; simp [Matrix.toQuadraticForm'])
        have htop : Module.finrank ℝ (⊤ : Submodule ℝ (τ → ℝ)) =
            Module.finrank ℝ (τ → ℝ) := by simp
        rw [htop] at hdim
        omega
