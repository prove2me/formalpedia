-- Prove2me | solution 1 for CurveSymmetry.holoBasisVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:10:25.709777+00:00
-- url     : https://prove2.me/submissions/65269350-652a-44cc-a8d5-84d1e30e4b70

-- Solution generated from lean/HolomorphicBasis.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Theorems.Thm_CurveSymmetry_familyInfinity_shift_sq
import Theorems.Thm_CurveSymmetry_isHolomorphic_smul_dt_iff
import Theorems.Thm_CurveSymmetry_quadLocal_poly_unit
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X])
lemma quadEval_root (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    quadEval h c d hd (AdjoinRoot.root _) = d :=
  AdjoinRoot.lift_root _
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X])
lemma algebraMap_quadRing_apply (y : QuadRing h) :
    algebraMap (QuadRing h) (QuadField h) y = quadRingMap h y := rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityMap_t :
    familyInfinityMap m α (algebraMap ℂ[X] (QuadField (familyH m α)) X) =
      (algebraMap ℂ[X] (QuadField (familyH m (star α))) X)⁻¹ := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m α)),
    familyInfinityMap_of, RatFunc.algebraMap_X, ratInv_X, map_inv₀,
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m (star α))),
    RatFunc.algebraMap_X]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section Quad
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
lemma quadT_eq : quadT h = algebraMap (RatFunc ℂ) (QuadField h) RatFunc.X := by
  rw [quadT, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h), RatFunc.algebraMap_X]
end Quad
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma quadT_ne_zero (h : ℂ[X]) [Fact (Irreducible (quadRat h))] : quadT h ≠ 0 := by
  rw [quadT, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h)]
  exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
    (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- An element that becomes a unit of the local ring has its inverse there. -/
lemma quadLocal_inv_mem_of_isUnit {x : QuadRing h}
    (hx : IsUnit (algebraMap (QuadRing h) (quadLocalRing h c d hd) x)) :
    (algebraMap (QuadRing h) (QuadField h) x)⁻¹ ∈ quadLocalRing h c d hd := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hcoe : algebraMap (QuadRing h) (QuadField h) x * (y : QuadField h) = 1 := by
    have hc1 := congrArg (fun z : quadLocalRing h c d hd => (z : QuadField h)) hy
    simpa using hc1
  rw [inv_eq_of_mul_eq_one_right hcoe]
  exact y.2
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- The root `w` is nonzero in the function field: `w² = h ≠ 0`. -/
lemma quadRoot_ne_zero : AdjoinRoot.root (quadRat h) ≠ 0 := by
  intro hzero
  have hsq := quadRoot_sq h
  rw [hzero, zero_pow two_ne_zero] at hsq
  have hne : algebraMap (RatFunc ℂ) (QuadField h) (algebraMap ℂ[X] (RatFunc ℂ) h) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
      (RatFunc.algebraMap_ne_zero (Fact.out : Squarefree h).ne_zero)
  exact hne hsq.symm
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma mem_holomorphicDifferentials (ω : Ω[QuadField (familyH m α)⁄ℂ]) :
    ω ∈ holomorphicDifferentials m α ↔ IsHolomorphic ω :=
  Iff.rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Point
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- Polynomials in `t` lie in every point place's local ring. -/
lemma quadLocal_poly_mem (p : ℂ[X]) :
    algebraMap ℂ[X] (QuadField h) p ∈ quadLocalRing h c d hd := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]
  exact Subalgebra.algebraMap_mem _ _
end Point
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Point
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- The root `w` lies in every point place's local ring. -/
lemma quadLocal_root_mem : AdjoinRoot.root (quadRat h) ∈ quadLocalRing h c d hd := by
  rw [← quadRingMap_root, ← algebraMap_quadRing_apply]
  exact Subalgebra.algebraMap_mem _ _
end Point
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Point
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- Where `d ≠ 0`, the root `w` is a unit of the local ring. -/
lemma quadLocal_root_inv_mem (hdne : d ≠ 0) :
    (AdjoinRoot.root (quadRat h))⁻¹ ∈ quadLocalRing h c d hd := by
  have hmem : AdjoinRoot.root (quadPoly h) ∈ (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, quadEval_root]
    exact hdne
  have := quadLocal_inv_mem_of_isUnit h c d hd
    (IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hmem⟩)
  rwa [algebraMap_quadRing_apply, quadRingMap_root] at this
end Point
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- The chart sends `t` to `1/s` and `w` to `w'·s^(−(m+1))`. -/
lemma familyInfinityMap_holoCoeff (i : ℕ) :
    familyInfinityMap m α (holoCoeff m α i) =
      (quadT (familyH m (star α)))⁻¹ ^ i *
        (AdjoinRoot.root (quadRat (familyH m (star α))) *
          (quadT (familyH m (star α)))⁻¹ ^ (m + 1))⁻¹ := by
  rw [holoCoeff, map_mul, map_pow, map_inv₀, familyInfinityMap_root]
  have ht : familyInfinityMap m α (quadT (familyH m α)) = (quadT (familyH m (star α)))⁻¹ := by
    rw [quadT, familyInfinityMap_t, quadT]
  rw [ht, map_inv₀, ← quadT_eq]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution (i : ℕ) (hi : i < m) :
    holoBasisVec m α i ∈ holomorphicDifferentials m α := by
  rw [mem_holomorphicDifferentials, holoBasisVec, isHolomorphic_smul_dt_iff]
  have hw := quadRoot_ne_zero (familyH m α)
  refine ⟨fun c d hd => ⟨fun hc => ?_, fun _ => ?_⟩, ?_⟩
  · -- unramified: `w` is a unit there
    have hdne : d ≠ 0 := by
      intro hzero
      rw [hzero] at hd
      exact hc (by linear_combination -hd)
    rw [holoCoeff]
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ?_ i)
      (quadLocal_root_inv_mem _ c d hd hdne)
    rw [quadT]
    exact quadLocal_poly_mem _ c d hd X
  · -- ramified: `(tⁱ/w)·w = tⁱ`
    rw [holoCoeff, mul_assoc, inv_mul_cancel₀ hw, mul_one]
    refine Subalgebra.pow_mem _ ?_ i
    rw [quadT]
    exact quadLocal_poly_mem _ c d hd X
  · -- infinity: `φ(tⁱ/w)/w'³ = w'^(2j)·k^(−(j+2))` with `m = i + 1 + j`
    obtain ⟨j, rfl⟩ : ∃ j, m = i + 1 + j := ⟨m - (i + 1), by omega⟩
    obtain ⟨k₀, hk0, hsk⟩ := familyInfinity_shift_sq (m := i + 1 + j) (α := α)
    have hw' := quadRoot_ne_zero (familyH (i + 1 + j) (star α))
    have hs := quadT_ne_zero (familyH (i + 1 + j) (star α))
    have hk : algebraMap ℂ[X] (QuadField (familyH (i + 1 + j) (star α))) k₀ ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hsk
      exact hw' (pow_eq_zero_iff two_ne_zero |>.mp hsk.symm)
    have hsval : quadT (familyH (i + 1 + j) (star α)) =
        AdjoinRoot.root (quadRat (familyH (i + 1 + j) (star α))) ^ 2 *
          (algebraMap ℂ[X] (QuadField (familyH (i + 1 + j) (star α))) k₀)⁻¹ := by
      rw [← hsk, mul_assoc, mul_inv_cancel₀ hk, mul_one]
    set S := quadT (familyH (i + 1 + j) (star α)) with hSdef
    set W := AdjoinRoot.root (quadRat (familyH (i + 1 + j) (star α))) with hWdef
    set Kk := algebraMap ℂ[X] (QuadField (familyH (i + 1 + j) (star α))) k₀
    have hA : familyInfinityMap (i + 1 + j) α (holoCoeff (i + 1 + j) α i) * (W ^ 3)⁻¹ =
        S ^ (j + 2) * (W ^ 4)⁻¹ := by
      rw [familyInfinityMap_holoCoeff, ← hSdef, ← hWdef]
      field_simp
      rw [one_div, inv_pow, inv_pow, div_eq_mul_inv, inv_inv,
        show i + 1 + j + 1 = i + (j + 2) by ring, pow_add,
        inv_mul_cancel_left₀ (pow_ne_zero i hs)]
    have hval : familyInfinityMap (i + 1 + j) α (holoCoeff (i + 1 + j) α i) * (W ^ 3)⁻¹ =
        W ^ (2 * j) * Kk⁻¹ ^ (j + 2) := by
      rw [hA, hsval]
      generalize Kk⁻¹ = Kinv
      rw [mul_pow, ← pow_mul, show 2 * (j + 2) = 2 * j + 4 by ring, pow_add]
      field_simp
    rw [hval]
    obtain ⟨-, hkinv⟩ := quadLocal_poly_unit (familyH (i + 1 + j) (star α)) 0 0
      (familyH_star_zero_point (i + 1 + j) α) k₀ hk0
    exact Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (quadLocal_root_mem _ 0 0 _) _)
      (Subalgebra.pow_mem _ hkinv _)
end

#print axioms solution
