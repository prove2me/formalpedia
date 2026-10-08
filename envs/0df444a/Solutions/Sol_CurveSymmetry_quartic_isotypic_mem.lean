-- Prove2me | solution 1 for CurveSymmetry.quartic_isotypic_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:30.672413+00:00
-- url     : https://prove2.me/submissions/fc5dbc95-d6ff-40ef-88a3-6185a4ff3c29

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
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticRot_I : quarticRot quarticI = quarticI :=
  quarticRot.commutes _
end Quartic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
theorem solution {V : Submodule ℂ K₄} (hV : ∀ G ∈ V, quarticRot G ∈ V)
    {G₀ G₁ G₂ G₃ : K₄} (h₀ : quarticRot G₀ = quarticI * G₀) (h₁ : quarticRot G₁ = -G₁)
    (h₂ : quarticRot G₂ = -(quarticI * G₂)) (h₃ : quarticRot G₃ = G₃)
    (hF : G₀ + G₁ + G₂ + G₃ ∈ V) : G₀ ∈ V ∧ G₁ ∈ V ∧ G₂ ∈ V ∧ G₃ ∈ V := by
  have hI := quarticI_sq
  have hIm : ∀ G ∈ V, quarticI * G ∈ V := fun G hG => by
    rw [← Algebra.smul_def]
    exact V.smul_mem _ hG
  have h4 : ∀ G : K₄, 4 * G ∈ V → G ∈ V := fun G hG => by
    have h4G : (4 : K₄) * G = (4 : ℂ) • G := by rw [Algebra.smul_def, map_ofNat]
    rw [h4G] at hG
    have := V.smul_mem (4 : ℂ)⁻¹ hG
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at this
  have e1 : quarticRot (G₀ + G₁ + G₂ + G₃) = quarticI * G₀ - G₁ - quarticI * G₂ + G₃ := by
    simp only [map_add, h₀, h₁, h₂, h₃]
    ring
  have e2 : quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) = -G₀ + G₁ - G₂ + G₃ := by
    rw [e1]
    simp only [map_add, map_sub, map_mul, quarticRot_I, h₀, h₁, h₂, h₃]
    linear_combination (G₀ + G₂) * hI
  have e3 : quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) =
      -(quarticI * G₀) - G₁ + quarticI * G₂ + G₃ := by
    rw [e2]
    simp only [map_add, map_sub, map_neg, h₀, h₁, h₂, h₃]
    ring
  have m1 := hV _ hF
  have m2 := hV _ m1
  have m3 := hV _ m2
  refine ⟨h4 _ ?_, h4 _ ?_, h4 _ ?_, h4 _ ?_⟩
  · have h : 4 * G₀ = G₀ + G₁ + G₂ + G₃ - quarticI * quarticRot (G₀ + G₁ + G₂ + G₃) -
        quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) +
        quarticI * quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) := by
      rw [e3, e2, e1]
      linear_combination 2 * (G₀ - G₂) * hI
    rw [h]
    exact add_mem (sub_mem (sub_mem hF (hIm _ m1)) m2) (hIm _ m3)
  · have h : 4 * G₁ = G₀ + G₁ + G₂ + G₃ - quarticRot (G₀ + G₁ + G₂ + G₃) +
        quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) -
        quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) := by
      rw [e3, e2, e1]
      ring
    rw [h]
    exact sub_mem (add_mem (sub_mem hF m1) m2) m3
  · have h : 4 * G₂ = G₀ + G₁ + G₂ + G₃ + quarticI * quarticRot (G₀ + G₁ + G₂ + G₃) -
        quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) -
        quarticI * quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) := by
      rw [e3, e2, e1]
      linear_combination 2 * (G₂ - G₀) * hI
    rw [h]
    exact sub_mem (sub_mem (add_mem hF (hIm _ m1)) m2) (hIm _ m3)
  · have h : 4 * G₃ = G₀ + G₁ + G₂ + G₃ + quarticRot (G₀ + G₁ + G₂ + G₃) +
        quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) +
        quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) := by
      rw [e3, e2, e1]
      ring
    rw [h]
    exact add_mem (add_mem (add_mem hF m1) m2) m3
end

#print axioms solution
