-- Prove2me | solution 1 for CurveSymmetry.fermat_regularAt_infinity_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:50.218978+00:00
-- url     : https://prove2.me/submissions/b98acd2b-a653-4813-90cb-6a33e508f8e8

-- Solution generated from lean/FermatInfinity.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
import Definitions.Def_CurveSymmetry_11_KummerLocal
import Definitions.Def_CurveSymmetry_12_FermatGenus
import Theorems.Thm_CurveSymmetry_kummer_regularAt_unramified
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
import Mathlib.LinearAlgebra.Dimension.Finrank
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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
section Transport
variable {K L : Type*} [Field K] [Algebra ℂ K] [Field L] [Algebra ℂ L]
/-- Regularity at a pulled-back place is regularity of the transported differential. -/
theorem mem_regularAt_comap_iff (e : K ≃ₐ[ℂ] L) (O : ValuationSubring L) (ω : Ω[K⁄ℂ]) :
    ω ∈ regularAt (O.comap (e : K →+* L)) ↔ kaehlerTransport e ω ∈ regularAt O := by
  refine ⟨kaehlerTransport_mem_regularAt e O, fun hω => ?_⟩
  have hO : (O.comap (e : K →+* L)).comap (e.symm : L →+* K) = O := by
    ext y
    simp [ValuationSubring.mem_comap]
  rw [← hO] at hω
  have hback := kaehlerTransport_mem_regularAt e.symm (O.comap (e : K →+* L)) hω
  rwa [kaehlerTransport_symm_apply] at hback
end Transport
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
lemma mem_kummerPlace_iff (z : KummerField n f) :
    z ∈ kummerPlace a b hb ↔ z ∈ kummerLocalRing a b hb :=
  Iff.rfl
end Local
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
lemma fermatInfinityMap_x : fermatInfinityMap quarticX = dualS⁻¹ := by
  rw [quarticX, kummerX_eq, fermatInfinityMap_of, ratInv_X, map_inv₀, ← dualS_eq]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
lemma fermatDual_eval_zero : fermatDual.eval 0 ≠ 0 := by
  simp [fermatDual]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
theorem solution (F : K₄) :
    F • KaehlerDifferential.D ℂ K₄ quarticX ∈ regularAt fermatInfinityPlace ↔
      fermatInfinityMap F * (dualS⁻¹) ^ 2 ∈ dualLocalRing := by
  rw [fermatInfinityPlace, mem_regularAt_comap_iff, kaehlerTransport_smul, kaehlerTransport_D,
    fermatInfinityAlgEquiv_apply, fermatInfinityAlgEquiv_apply, fermatInfinityMap_x,
    Derivation.leibniz_inv, smul_smul,
    kummer_regularAt_unramified (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow
      fermatDual_eval_zero, mem_kummerPlace_iff, mul_neg]
  exact neg_mem_iff
end

#print axioms solution
