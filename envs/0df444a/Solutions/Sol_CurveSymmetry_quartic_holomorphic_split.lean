-- Prove2me | solution 1 for CurveSymmetry.quartic_holomorphic_split
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:59.790801+00:00
-- url     : https://prove2.me/submissions/bc750241-a47a-4db8-b8bc-ae71ed292754

-- Solution generated from lean/FermatSplit.lean (curve-symmetry-lean): inlined helpers in
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
import Theorems.Thm_CurveSymmetry_quartic_isotypic_mem
import Theorems.Thm_CurveSymmetry_quartic_mul_y3_mem_range
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
open Polynomial TensorProduct
section BaseChange
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T] {ι : Type*} [Unique ι]
omit [Unique ι] in
@[simp] lemma kaehlerBasisOfEtale_apply (b : Module.Basis ι S Ω[S⁄R]) (i : ι) :
    kaehlerBasisOfEtale R S T b i = KaehlerDifferential.map R R S T (b i) := by
  simp [kaehlerBasisOfEtale, Module.Basis.baseChange_apply,
    KaehlerDifferential.mapBaseChange_tmul]
end BaseChange
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
@[simp] lemma polynomialKaehlerBasis_apply (i : Unit) :
    polynomialKaehlerBasis i = KaehlerDifferential.D ℂ ℂ[X] X := by
  simp [polynomialKaehlerBasis, Module.Basis.singleton_apply,
    KaehlerDifferential.polynomialEquiv_symm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
@[simp] lemma ratFuncKaehlerBasis_apply (i : Unit) :
    ratFuncKaehlerBasis i = KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X := by
  rw [ratFuncKaehlerBasis, kaehlerBasisOfEtale_apply, polynomialKaehlerBasis_apply,
    KaehlerDifferential.map_D, RatFunc.algebraMap_X]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Ring
variable (n : ℕ) (f : ℂ[X])
lemma kummerRingMap_root :
    kummerRingMap n f (AdjoinRoot.root (kummerPoly n f)) = AdjoinRoot.root (kummerRat n f) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _
end Ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Field
variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]
@[simp] lemma kummerKaehlerBasis_apply (i : Unit) :
    kummerKaehlerBasis n f i = KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
  rw [kummerKaehlerBasis, kaehlerBasisOfEtale_apply, ratFuncKaehlerBasis_apply,
    KaehlerDifferential.map_D, kummerX_eq]
end Field
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Field
variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]
theorem kummer_kaehler_span_eq_top :
    Submodule.span (KummerField n f)
      {KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f)} = ⊤ := by
  have hrange : Set.range (kummerKaehlerBasis n f) =
      {KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f)} := by
    rw [Set.range_unique, kummerKaehlerBasis_apply]
  rw [← hrange]
  exact (kummerKaehlerBasis n f).span_eq
end Field
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Field
variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]
/-- Every differential is a multiple of `dx`. -/
theorem kummer_exists_smul_D_x (ω : Ω[KummerField n f⁄ℂ]) :
    ∃ c : KummerField n f, ω = c • KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
  have hmem : ω ∈ Submodule.span (KummerField n f)
      {KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f)} := by
    rw [kummer_kaehler_span_eq_top]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩
end Field
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quartic_polynomial_injective : Function.Injective (algebraMap ℂ[X] K₄) := by
  rw [IsScalarTower.algebraMap_eq ℂ[X] (RatFunc ℂ) K₄]
  exact (algebraMap (RatFunc ℂ) K₄).injective.comp (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticY_ne_zero : quarticY ≠ 0 := by
  intro h0
  have h := kummerRoot_pow 4 fermatQuartic
  rw [show AdjoinRoot.root (kummerRat 4 fermatQuartic) = quarticY from rfl, h0,
    zero_pow (by norm_num)] at h
  have hf : (C 2 - X ^ 4 : ℂ[X]) = 0 := quartic_polynomial_injective (by rw [map_zero]; exact h.symm)
  have := congrArg (eval 0) hf
  simp at this
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Reduction
/-- An element of the Kummer coordinate ring given by a polynomial of degree less than `n` in `Y`
is `Σ gⱼ(x)·yʲ` in the function field. -/
lemma kummerRingMap_mk_eq_sum {n : ℕ} {f : ℂ[X]} (g : ℂ[X][X]) (hg : g.natDegree < n) :
    kummerRingMap n f (AdjoinRoot.mk (kummerPoly n f) g) =
      ∑ j ∈ Finset.range n, algebraMap ℂ[X] (KummerField n f) (g.coeff j) *
        AdjoinRoot.root (kummerRat n f) ^ j := by
  rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, kummerRingMap_root, aeval_def,
    eval₂_eq_sum_range' _ hg]
end Reduction
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Reduction
/-- Every element of the Kummer coordinate ring is `Σ_{j<n} aⱼ(x)·yʲ` in the function field. -/
lemma kummer_exists_sum {n : ℕ} {f : ℂ[X]} (hn : n ≠ 0) (r : KummerRing n f) :
    ∃ a : ℕ → ℂ[X], kummerRingMap n f r =
      ∑ j ∈ Finset.range n, algebraMap ℂ[X] (KummerField n f) (a j) *
        AdjoinRoot.root (kummerRat n f) ^ j := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective r
  have hm := kummerPoly_monic n f hn
  have hdeg : (kummerPoly n f).natDegree = n := by
    show (X ^ n - C f).natDegree = n
    exact natDegree_X_pow_sub_C
  have hne : kummerPoly n f ≠ 1 := fun h => hn (by rw [← hdeg, h, natDegree_one])
  have hmk : AdjoinRoot.mk (kummerPoly n f) g =
      AdjoinRoot.mk (kummerPoly n f) (g %ₘ kummerPoly n f) :=
    (AdjoinRoot.mk_leftInverse hm (AdjoinRoot.mk _ g)).symm.trans
      (congrArg (AdjoinRoot.mk _) (AdjoinRoot.modByMonicHom_mk hm g))
  refine ⟨fun j => (g %ₘ kummerPoly n f).coeff j, ?_⟩
  rw [hmk]
  refine kummerRingMap_mk_eq_sum _ ?_
  have := natDegree_modByMonic_lt g hm hne
  rwa [hdeg] at this
end Reduction
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_apply (z : K₄) : quarticRot z = quarticRotHom z :=
  rfl
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_ratFunc (q : RatFunc ℂ) :
    quarticRot (algebraMap (RatFunc ℂ) K₄ q) = algebraMap (RatFunc ℂ) K₄ q :=
  quarticRotHom.commutes q
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_poly (p : ℂ[X]) :
    quarticRot (algebraMap ℂ[X] K₄ p) = algebraMap ℂ[X] K₄ p := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) K₄, quarticRot_ratFunc]
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_x : quarticRot quarticX = quarticX := by
  show quarticRot (kummerX 4 fermatQuartic) = kummerX 4 fermatQuartic
  rw [kummerX_eq, quarticRot_ratFunc]
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_y : quarticRot quarticY = quarticI * quarticY := by
  rw [quarticRot_apply]
  exact AdjoinRoot.liftAlgHom_root (kummerRat 4 fermatQuartic) _ _ _
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
/-- `σ` carries holomorphic `F·dx` to holomorphic `σ(F)·dx`, since `σ(x) = x`. -/
lemma quarticRot_mem {F : K₄}
    (hF : F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄) :
    quarticRot F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄ := by
  have h := kaehlerTransport_mem_holomorphicSpace quarticRot hF
  rwa [kaehlerTransport_smul, kaehlerTransport_D, quarticRot_x] at h
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
/-- `σ(p(x)·yʲ/y³) = iʲ⁺¹·p(x)·yʲ/y³`. -/
lemma quarticRot_term (p : ℂ[X]) (j : ℕ) :
    quarticRot (quarticTerm p j) = quarticI ^ (j + 1) * quarticTerm p j := by
  have hI := quarticI_sq
  have hinv : quarticI⁻¹ = -quarticI :=
    inv_eq_of_mul_eq_one_right (by linear_combination -hI)
  rw [quarticTerm, map_mul, map_mul, map_pow, map_pow, map_inv₀, quarticRot_poly, quarticRot_y,
    mul_inv, hinv]
  linear_combination
    (-(algebraMap ℂ[X] K₄ p * quarticI ^ (j + 1) * quarticY ^ j * quarticY⁻¹ ^ 3)) * hI
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_term_zero (p : ℂ[X]) :
    quarticRot (quarticTerm p 0) = quarticI * quarticTerm p 0 := by
  rw [quarticRot_term, zero_add, pow_one]
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_term_one (p : ℂ[X]) : quarticRot (quarticTerm p 1) = -quarticTerm p 1 := by
  rw [quarticRot_term]
  linear_combination quarticTerm p 1 * quarticI_sq
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_term_two (p : ℂ[X]) :
    quarticRot (quarticTerm p 2) = -(quarticI * quarticTerm p 2) := by
  rw [quarticRot_term]
  linear_combination quarticI * quarticTerm p 2 * quarticI_sq
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_term_three (p : ℂ[X]) : quarticRot (quarticTerm p 3) = quarticTerm p 3 := by
  rw [quarticRot_term]
  linear_combination (quarticI ^ 2 - 1) * quarticTerm p 3 * quarticI_sq
end Quartic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
theorem solution {ω : Ω[K₄⁄ℂ]} (hω : ω ∈ holomorphicSpace K₄) :
    ∃ a₀ a₁ a₂ a₃ : ℂ[X],
      ω = (quarticTerm a₀ 0 + quarticTerm a₁ 1 + quarticTerm a₂ 2 + quarticTerm a₃ 3) •
        KaehlerDifferential.D ℂ K₄ quarticX ∧
      quarticTerm a₀ 0 ∈ quarticHoloCoeffs ∧ quarticTerm a₁ 1 ∈ quarticHoloCoeffs ∧
      quarticTerm a₂ 2 ∈ quarticHoloCoeffs ∧ quarticTerm a₃ 3 ∈ quarticHoloCoeffs := by
  obtain ⟨F, rfl⟩ := kummer_exists_smul_D_x 4 fermatQuartic ω
  obtain ⟨r, hr⟩ := quartic_mul_y3_mem_range hω
  obtain ⟨a, ha⟩ := kummer_exists_sum (n := 4) (f := fermatQuartic) (by norm_num) r
  have h := ha.symm.trans hr
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have hy3 : quarticY ^ 3 * quarticY⁻¹ ^ 3 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ quarticY_ne_zero, one_pow]
  have hF : F = quarticTerm (a 0) 0 + quarticTerm (a 1) 1 + quarticTerm (a 2) 2 +
      quarticTerm (a 3) 3 := by
    calc F = F * quarticY ^ 3 * quarticY⁻¹ ^ 3 := by rw [mul_assoc, hy3, mul_one]
      _ = _ := by
        rw [← h]
        simp only [quarticTerm]
        ring
  have hmem : F ∈ quarticHoloCoeffs := hω
  rw [hF] at hmem
  obtain ⟨m0, m1, m2, m3⟩ := quartic_isotypic_mem (fun G hG => quarticRot_mem hG)
    (quarticRot_term_zero _) (quarticRot_term_one _) (quarticRot_term_two _)
    (quarticRot_term_three _) hmem
  exact ⟨a 0, a 1, a 2, a 3, by rw [← hF], m0, m1, m2, m3⟩
end

#print axioms solution
