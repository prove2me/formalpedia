-- Prove2me | solution 1 for CurveSymmetry.quartic_holomorphicSpace_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:08:18.659714+00:00
-- url     : https://prove2.me/submissions/69f46562-2896-431e-9320-3214cf54ce00

-- Solution generated from lean/FermatGenus.lean (curve-symmetry-lean): inlined helpers in
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
import Theorems.Thm_CurveSymmetry_primeValuationSubring_ne_top
import Theorems.Thm_CurveSymmetry_quarticHolo_mem
import Theorems.Thm_CurveSymmetry_quarticTerm_natDegree_le
import Theorems.Thm_CurveSymmetry_quartic_holomorphic_split
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
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
lemma kummerLocal_ringElem_mem (r : KummerRing n f) :
    algebraMap (KummerRing n f) (KummerField n f) r ∈ kummerLocalRing a b hb :=
  Subalgebra.algebraMap_mem _ _
end Local
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
lemma kummerLocal_const_mem (z : ℂ) :
    algebraMap ℂ (KummerField n f) z ∈ kummerLocalRing a b hb := by
  rw [IsScalarTower.algebraMap_apply ℂ (KummerRing n f) (KummerField n f)]
  exact kummerLocal_ringElem_mem a b hb _
end Local
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]
section Local
variable (a b : ℂ) (hb : b ^ n = f.eval a)
/-- **R01c-2b**: the place at a point is a place over `ℂ` in the sense of R01a. -/
lemma kummerPlace_isComplexPlace : IsComplexPlace (kummerPlace a b hb) :=
  ⟨primeValuationSubring_ne_top _ (kummerEval_ker_ne_bot a b hb), kummerLocal_const_mem a b hb⟩
end Local
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
lemma fermatInfinityPlace_isComplexPlace : IsComplexPlace fermatInfinityPlace :=
  (kummerPlace_isComplexPlace (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow).comap _
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma mem_quarticHoloCoeffs {F : K₄} :
    F ∈ quarticHoloCoeffs ↔ F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄ :=
  Iff.rfl
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
/-- A holomorphic piece `p(x)·yʲ·dx/y³` has `p = 0` or `deg p + j ≤ 1`. -/
lemma quarticTerm_holo_natDegree {p : ℂ[X]} {j : ℕ} (h : quarticTerm p j ∈ quarticHoloCoeffs) :
    p = 0 ∨ p.natDegree + j ≤ 1 := by
  by_cases hp : p = 0
  · exact Or.inl hp
  · exact Or.inr (quarticTerm_natDegree_le hp
      (mem_holomorphicSpace.mp (mem_quarticHoloCoeffs.mp h) _ fermatInfinityPlace_isComplexPlace))
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
/-- With `a₀ = c₁x + c₀`, `a₁ = e` and `a₂ = a₃ = 0`, the differential is
`c₀·dx/y³ + c₁·x·dx/y³ + e·dx/y²`. -/
lemma quartic_span_combination (c₀ c₁ e : ℂ) :
    (quarticTerm (C c₁ * X + C c₀) 0 + quarticTerm (C e) 1 + quarticTerm 0 2 +
        quarticTerm 0 3) • KaehlerDifferential.D ℂ K₄ quarticX =
      c₀ • quarticHolo 0 + c₁ • quarticHolo 1 + e • quarticHolo 2 := by
  have hC : ∀ c : ℂ, algebraMap ℂ[X] K₄ (C c) = algebraMap ℂ K₄ c := fun c =>
    (IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄ c).symm
  have hX : algebraMap ℂ[X] K₄ X = quarticX := rfl
  have h0 : quarticHoloNum 0 = 1 := rfl
  have h1 : quarticHoloNum 1 = quarticX := rfl
  have h2 : quarticHoloNum 2 = quarticY := rfl
  simp only [quarticHolo, h0, h1, h2, ← smul_assoc, ← add_smul, Algebra.smul_def]
  congr 1
  simp only [quarticTerm, map_add, map_mul, map_zero, hC, hX]
  ring
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
/-- **R01e-3**: every holomorphic differential of the quartic is a combination of `dx/y³`,
`x·dx/y³` and `dx/y²`. -/
theorem quartic_holomorphicSpace_le_span :
    holomorphicSpace K₄ ≤ Submodule.span ℂ (Set.range quarticHolo) := by
  intro ω hω
  obtain ⟨a₀, a₁, a₂, a₃, rfl, h₀, h₁, h₂, h₃⟩ := quartic_holomorphic_split hω
  have ha₂ : a₂ = 0 := (quarticTerm_holo_natDegree h₂).resolve_right (by omega)
  have ha₃ : a₃ = 0 := (quarticTerm_holo_natDegree h₃).resolve_right (by omega)
  have ha₁ : a₁ = C (a₁.coeff 0) := by
    refine eq_C_of_natDegree_le_zero ?_
    rcases quarticTerm_holo_natDegree h₁ with h | h
    · rw [h, natDegree_zero]
    · omega
  have ha₀ : a₀ = C (a₀.coeff 1) * X + C (a₀.coeff 0) := by
    refine eq_X_add_C_of_natDegree_le_one ?_
    rcases quarticTerm_holo_natDegree h₀ with h | h
    · rw [h, natDegree_zero]
      exact zero_le_one
    · omega
  rw [ha₂, ha₃, ha₁, ha₀, quartic_span_combination]
  exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
end Quartic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual
theorem solution :
    holomorphicSpace K₄ = Submodule.span ℂ (Set.range quarticHolo) :=
  le_antisymm quartic_holomorphicSpace_le_span
    (Submodule.span_le.mpr (Set.range_subset_iff.mpr quarticHolo_mem))
end

#print axioms solution
