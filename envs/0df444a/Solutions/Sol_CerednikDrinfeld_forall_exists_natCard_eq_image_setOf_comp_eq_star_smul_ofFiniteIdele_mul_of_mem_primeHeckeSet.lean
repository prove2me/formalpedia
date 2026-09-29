-- Prove2me | solution 1 for CerednikDrinfeld.forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/bb40631c-e244-5112-8f82-69b1bf79f853

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_Submodule_ofFiniteIdele_diagonal_mul
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm"

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve

namespace Ws3
namespace StepDictBody

noncomputable section

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}

abbrev LHSPred (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (ℓ : ℕ)
    (J : Submodule ℤ ℍ[ℚ, a, b]) : Prop :=
  (∃ h ∈ primeHeckeSet Λ ℓ, J = Submodule.ofFiniteIdele Λ (x * h)) ∧
    ∃ e : (ℍ[ℚ, a, b])ˣ, J = e • Submodule.ofFiniteIdele Λ y

abbrev RHSPred (W W' : WeierstrassCurve κ) (ℓ : ℕ) (C : AddSubgroup W.toAffine.Point) : Prop :=
  Nat.card C = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ W W', ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W,
    ψ.ker = C ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _

section Dictionary

variable (X₀ W : WeierstrassCurve κ)
variable (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
variable (χ : X₀.toAffine.Point →+ W.toAffine.Point) (d : (ℍ[ℚ, a, b])ˣ)

def homsInto (J : Submodule ℤ ℍ[ℚ, a, b]) : Set (W.toAffine.Point →+ X₀.toAffine.Point) :=
  {ρ | ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀ ∧
    ∃ e : ↥(WeierstrassCurve.rationalEndSubring κ X₀),
      ((e : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) :
          AddMonoid.End (X₀.baseChange κ).toAffine.Point) = ρ.comp χ ∧
        θ e ∈ star '' ((d • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])}

def killed (J : Submodule ℤ ℍ[ℚ, a, b]) : AddSubgroup W.toAffine.Point :=
  ⨅ ρ ∈ homsInto X₀ W θ χ d J, AddMonoidHom.ker ρ

def annHoms (C : AddSubgroup W.toAffine.Point) : Set (W.toAffine.Point →+ X₀.toAffine.Point) :=
  {ρ | ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀ ∧ C ≤ AddMonoidHom.ker ρ}

def annEnds (C : AddSubgroup W.toAffine.Point) : Set ↥(WeierstrassCurve.rationalEndSubring κ X₀) :=
  {e | ∃ ρ ∈ annHoms X₀ W C,
    ((e : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) :
        AddMonoid.End (X₀.baseChange κ).toAffine.Point) = ρ.comp χ}

def annLattice (C : AddSubgroup W.toAffine.Point) : Submodule ℤ ℍ[ℚ, a, b] :=
  d⁻¹ • Submodule.span ℤ (star '' (θ '' annEnds X₀ W χ C))

end Dictionary

section StageA

variable (X₀ W : WeierstrassCurve κ)
variable (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
variable (χ : X₀.toAffine.Point →+ W.toAffine.Point) (d : (ℍ[ℚ, a, b])ˣ)

def psi : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+ ℍ[ℚ, a, b] where
  toFun e := ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star (θ e)
  map_zero' := by simp
  map_add' e₁ e₂ := by simp [mul_add]

theorem psi_apply (e : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) :
    psi X₀ θ d e = ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star (θ e) := rfl

def endsOf (S : Set (W.toAffine.Point →+ X₀.toAffine.Point)) :
    Set ↥(WeierstrassCurve.rationalEndSubring κ X₀) :=
  {e | ∃ ρ ∈ S, ((e : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) :
      AddMonoid.End (X₀.baseChange κ).toAffine.Point) = ρ.comp χ}

def latticeOf (S : Set (W.toAffine.Point →+ X₀.toAffine.Point)) : Submodule ℤ ℍ[ℚ, a, b] :=
  Submodule.span ℤ (psi X₀ θ d '' endsOf X₀ W χ S)

variable {X₀ W θ χ d}

theorem psi_injective (hθ : Function.Injective θ) : Function.Injective (psi X₀ θ d) := by
  intro e₁ e₂ h
  exact hθ (star_injective ((Units.mul_right_inj _).mp h))

theorem mem_star_image_smul_iff (J : Submodule ℤ ℍ[ℚ, a, b]) (w : ℍ[ℚ, a, b]) :
    w ∈ star '' ((d • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ↔
      ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star w ∈ J := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Units.smul_def, Submodule.mem_smul_pointwise_iff_exists] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    simpa [smul_eq_mul, ← mul_assoc] using hj
  · intro h
    refine ⟨star w, ?_, star_star w⟩
    rw [SetLike.mem_coe, Units.smul_def, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨_, h, by simp [smul_eq_mul, ← mul_assoc]⟩

theorem mem_homsInto_iff (J : Submodule ℤ ℍ[ℚ, a, b]) (ρ : W.toAffine.Point →+ X₀.toAffine.Point) :
    ρ ∈ homsInto X₀ W θ χ d J ↔ ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀ ∧
      ∃ e : ↥(WeierstrassCurve.rationalEndSubring κ X₀),
        ((e : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) :
            AddMonoid.End (X₀.baseChange κ).toAffine.Point) = ρ.comp χ ∧ psi X₀ θ d e ∈ J := by
  simp only [homsInto, Set.mem_setOf_eq, mem_star_image_smul_iff, psi_apply]

theorem annEnds_eq : annEnds X₀ W χ = endsOf X₀ W χ ∘ annHoms X₀ W := rfl

theorem annLattice_eq_latticeOf (C : AddSubgroup W.toAffine.Point) :
    annLattice X₀ W θ χ d C = latticeOf X₀ W θ χ d (annHoms X₀ W C) := by
  rw [annLattice, latticeOf, Units.smul_def, Submodule.pointwise_smul_def, Submodule.map_span, Set.image_image,
    Set.image_image]
  rfl

section WithHyp

variable [X₀.IsElliptic] [W.IsElliptic]

theorem comp_mem_rationalEndSubring (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W)
    {ρ : W.toAffine.Point →+ X₀.toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀) :
    (ρ.comp χ : AddMonoid.End (X₀.baseChange κ).toAffine.Point) ∈ WeierstrassCurve.rationalEndSubring κ X₀ :=
  Subring.subset_closure (WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W X₀ hχ hρ)

def compEnd (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W)
    {ρ : W.toAffine.Point →+ X₀.toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀) :
    ↥(WeierstrassCurve.rationalEndSubring κ X₀) :=
  ⟨_, comp_mem_rationalEndSubring hχ hρ⟩

@[scoped simp] theorem coe_compEnd (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W)
    {ρ : W.toAffine.Point →+ X₀.toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀) :
    ((compEnd hχ hρ : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) :
        AddMonoid.End (X₀.baseChange κ).toAffine.Point) = ρ.comp χ := rfl

theorem compEnd_mem_kernelIdealSet (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W)
    {ρ : W.toAffine.Point →+ X₀.toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀) :
    compEnd hχ hρ ∈ WeierstrassCurve.kernelIdealSet κ X₀ W χ :=
  ⟨ρ, hρ, rfl⟩

theorem eq_compEnd (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W)
    {ρ : W.toAffine.Point →+ X₀.toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀)
    {e : ↥(WeierstrassCurve.rationalEndSubring κ X₀)}
    (he : ((e : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) :
        AddMonoid.End (X₀.baseChange κ).toAffine.Point) = ρ.comp χ) :
    e = compEnd hχ hρ :=
  Subtype.ext he

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

theorem psi_compEnd_mem (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W)
    (hχK : θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    {ρ : W.toAffine.Point →+ X₀.toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀) :
    psi X₀ θ d (compEnd hχ hρ) ∈ Submodule.ofFiniteIdele Λ x := by
  have h : θ (compEnd hχ hρ) ∈ θ '' WeierstrassCurve.kernelIdealSet κ X₀ W χ :=
    Set.mem_image_of_mem _ (compEnd_mem_kernelIdealSet hχ hρ)
  rwa [hχK, mem_star_image_smul_iff] at h

theorem exists_psi_compEnd_eq (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W)
    (hχK : θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    {z : ℍ[ℚ, a, b]} (hz : z ∈ Submodule.ofFiniteIdele Λ x) :
    ∃ ρ, ∃ hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀, psi X₀ θ d (compEnd hχ hρ) = z := by
  have h : star ((d : ℍ[ℚ, a, b]) * z) ∈
      star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
    rw [mem_star_image_smul_iff]; simpa [← mul_assoc] using hz
  rw [← hχK] at h
  obtain ⟨e, ⟨ρ, hρ, he⟩, hθe⟩ := h
  refine ⟨ρ, hρ, ?_⟩
  rw [← eq_compEnd hχ hρ he, psi_apply, hθe]
  simp [← mul_assoc]

theorem neg_mem_rationalHomSet_of_ker (hθ : Function.Injective θ)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχs : Function.Surjective χ)
    (hχK : θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    {ρ : W.toAffine.Point →+ X₀.toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀) :
    -ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀ := by
  have h1 : psi X₀ θ d (-compEnd hχ hρ) ∈ Submodule.ofFiniteIdele Λ x := by
    rw [map_neg]; exact Submodule.neg_mem _ (psi_compEnd_mem hχ hχK hρ)
  have h2 : θ (-compEnd hχ hρ) ∈ θ '' WeierstrassCurve.kernelIdealSet κ X₀ W χ := by
    rw [hχK, mem_star_image_smul_iff]; exact h1
  obtain ⟨e, ⟨ρ', hρ', he⟩, hθe⟩ := h2
  have hee : e = -compEnd hχ hρ := hθ hθe
  have h3 : ρ'.comp χ = (-ρ).comp χ := by
    rw [AddMonoidHom.neg_comp]
    have := congrArg (fun f : ↥(WeierstrassCurve.rationalEndSubring κ X₀) =>
      ((f : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) : AddMonoid.End (X₀.baseChange κ).toAffine.Point)) hee
    simp only [he, NegMemClass.coe_neg, coe_compEnd] at this
    exact this
  have h4 : ρ' = -ρ := (AddMonoidHom.cancel_right hχs).mp h3
  exact h4 ▸ hρ'

theorem latticeOf_homsInto (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W)
    (hχK : θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    {J : Submodule ℤ ℍ[ℚ, a, b]} (hJ : J ≤ Submodule.ofFiniteIdele Λ x) :
    latticeOf X₀ W θ χ d (homsInto X₀ W θ χ d J) = J := by
  refine le_antisymm ?_ ?_
  · rw [latticeOf, Submodule.span_le]
    rintro _ ⟨e, ⟨ρ, hρN, he⟩, rfl⟩
    rw [mem_homsInto_iff] at hρN
    obtain ⟨hρ, e', he', hmem⟩ := hρN
    rwa [eq_compEnd hχ hρ he, ← eq_compEnd hχ hρ he']
  · intro z hz
    obtain ⟨ρ, hρ, hρz⟩ := exists_psi_compEnd_eq hχ hχK (hJ hz)
    refine Submodule.subset_span ⟨compEnd hχ hρ, ⟨ρ, ?_, rfl⟩, hρz⟩
    rw [mem_homsInto_iff]
    exact ⟨hρ, compEnd hχ hρ, rfl, hρz ▸ hz⟩

theorem homsInto_latticeOf (hθ : Function.Injective θ)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχs : Function.Surjective χ)
    (S : AddSubgroup (W.toAffine.Point →+ X₀.toAffine.Point))
    (hS : (S : Set (W.toAffine.Point →+ X₀.toAffine.Point)) ⊆ WeierstrassCurve.rationalHomSet κ W X₀) :
    homsInto X₀ W θ χ d (latticeOf X₀ W θ χ d S) = S := by

  have key : ∀ z, z ∈ latticeOf X₀ W θ χ d (S : Set _) ↔
      ∃ ρ, ∃ hρS : ρ ∈ S, psi X₀ θ d (compEnd hχ (hS hρS)) = z := by
    intro z
    constructor
    · intro hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨e, ⟨ρ, hρS, he⟩, rfl⟩ := hw
        exact ⟨ρ, hρS, by rw [← eq_compEnd hχ (hS hρS) he]⟩
      | zero =>
        refine ⟨0, S.zero_mem, ?_⟩
        rw [← map_zero (psi X₀ θ d)]
        exact congrArg _ (Subtype.ext (by first | rfl | simp))
      | add u v _ _ hu hv =>
        obtain ⟨ρ, hρ, rfl⟩ := hu
        obtain ⟨σ, hσ, rfl⟩ := hv
        refine ⟨ρ + σ, S.add_mem hρ hσ, ?_⟩
        rw [← map_add]
        exact congrArg _ (Subtype.ext (by first | rfl | simp [AddMonoidHom.add_comp]))
      | smul n u _ hu =>
        obtain ⟨ρ, hρ, rfl⟩ := hu
        refine ⟨n • ρ, S.zsmul_mem hρ n, ?_⟩
        rw [← map_zsmul]
        exact congrArg _ (Subtype.ext (by first | rfl | simp | (simp; rfl)))
    · rintro ⟨ρ, hρS, rfl⟩
      exact Submodule.subset_span ⟨_, ⟨ρ, hρS, rfl⟩, rfl⟩
  ext ρ
  rw [mem_homsInto_iff]
  constructor
  · rintro ⟨hρ, e, he, hmem⟩
    obtain ⟨σ, hσS, hσ⟩ := (key _).mp hmem
    rw [eq_compEnd hχ hρ he] at hσ
    have hσρ : compEnd hχ (hS hσS) = compEnd hχ hρ := psi_injective hθ hσ
    have : σ = ρ := by
      rw [← AddMonoidHom.cancel_right hχs]
      exact congrArg (fun f : ↥(WeierstrassCurve.rationalEndSubring κ X₀) =>
        ((f : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) : AddMonoid.End (X₀.baseChange κ).toAffine.Point)) hσρ
    exact this ▸ hσS
  · intro hρS
    exact ⟨hS hρS, compEnd hχ (hS hρS), rfl, (key _).mpr ⟨ρ, hρS, rfl⟩⟩

end WithHyp

end StageA

theorem tmul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ)
    {c : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hc : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {u v : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hu : u ∈ Submodule.finiteAdeleBox Λ) (hv : v ∈ Submodule.finiteAdeleBox Λ) :
    u * v ∈ Submodule.finiteAdeleBox Λ := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hu'
    induction hv using AddSubgroup.closure_induction with
    | mem v hv' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hv'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_finiteAdeleBox (hΛ.mul_mem hz hz') fun w => mul_mem (hc w) (hc' w)
    | zero => rw [mul_zero]; exact zero_mem _
    | add v v' _ _ ihv ihv' => rw [mul_add]; exact add_mem ihv ihv'
    | neg v _ ihv =>
      convert neg_mem ihv using 1
      exact mul_neg (α := ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) _ _
  | zero => rw [zero_mul]; exact zero_mem _
  | add u u' _ _ ihu ihu' => rw [add_mul]; exact add_mem ihu ihu'
  | neg u _ ihu =>
    convert neg_mem ihu using 1
    exact neg_mul (α := ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) _ _

theorem mem_ofFiniteIdele_iff' (R : Submodule ℤ ℍ[ℚ, a, b])
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele R g ↔
      ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) *
        (z ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox R := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨t, ht, h⟩
    have h' : (g : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * t =
        z ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) := h
    rw [← h', Units.inv_mul_cancel_left]
    exact ht
  · intro h
    exact ⟨_, h, by simp⟩

theorem ofFiniteIdele_mul_le_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {ℓ : ℕ}
    {h : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hh : h ∈ primeHeckeSet Λ ℓ) :
    Submodule.ofFiniteIdele Λ (x * h) ≤ Submodule.ofFiniteIdele Λ x := by
  intro z hz
  rw [mem_ofFiniteIdele_iff'] at hz ⊢
  rw [mul_inv_rev, Units.val_mul, mul_assoc] at hz
  have := mul_mem_finiteAdeleBox hΛ hh.1 hz
  rwa [Units.mul_inv_cancel_left] at this

theorem zsmul_mem_ofFiniteIdele_mul_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {ℓ : ℕ}
    {h : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hh : h ∈ primeHeckeSet Λ ℓ)
    {z : ℍ[ℚ, a, b]} (hz : z ∈ Submodule.ofFiniteIdele Λ x) :
    (ℓ : ℤ) • z ∈ Submodule.ofFiniteIdele Λ (x * h) := by
  rw [mem_ofFiniteIdele_iff'] at hz ⊢
  rw [mul_inv_rev, Units.val_mul, mul_assoc]
  have e : ((ℓ : ℤ) • z) ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (ℓ : ℚ) • (z ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    rw [TensorProduct.smul_tmul', ← Int.cast_smul_eq_zsmul ℚ (ℓ : ℤ) z, Int.cast_natCast]
  rw [e, mul_smul_comm, mul_smul_comm, ← smul_mul_assoc]
  exact mul_mem_finiteAdeleBox hΛ hh.2.1 hz

theorem mem_finiteAdeleBox_of_mem_finiteIdeleStabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {u : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    (u : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
  have h1 : (u : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) •
      (1 : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      (u • (Submodule.finiteAdeleBox Λ : Set (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    refine Set.smul_mem_smul_set ?_
    rw [Algebra.TensorProduct.one_def]
    exact tmul_mem_finiteAdeleBox hΛ.one_mem fun v => one_mem _
  rw [MulAction.mem_stabilizer_iff.mp hu, smul_eq_mul, mul_one] at h1
  exact h1

theorem ofFiniteIdele_mul_ne_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {ℓ : ℕ}
    {h : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hh : h ∈ primeHeckeSet Λ ℓ) :
    Submodule.ofFiniteIdele Λ (x * h) ≠ Submodule.ofFiniteIdele Λ x := by
  intro heq
  have hst := (Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hΛ.fg hΛ.spanTop (x * h) x).mp heq
  rw [mul_inv_rev, inv_mul_cancel_right] at hst
  exact hh.2.2.1 (mem_finiteAdeleBox_of_mem_finiteIdeleStabilizer hΛ hst)

theorem not_forall_mem_ofFiniteIdele_mul_exists_eq_smul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {h : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hh : h ∈ primeHeckeSet Λ ℓ) :
    ¬ ∀ z ∈ Submodule.ofFiniteIdele Λ (x * h), ∃ w ∈ Submodule.ofFiniteIdele Λ x, z = (ℓ : ℤ) • w := by
  intro hall
  have hℓQ : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
  set δ : (ℍ[ℚ, a, b])ˣ := Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (ℓ : ℚ) hℓQ) with hδ
  have hδval : (δ : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hδ, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0]
    rfl
  have hδsmul : ∀ w : ℍ[ℚ, a, b], δ • w = (ℓ : ℤ) • w := fun w => by
    rw [Units.smul_def, hδval, smul_eq_mul, QuaternionAlgebra.coe_mul_eq_smul,
      ← Int.cast_smul_eq_zsmul ℚ (ℓ : ℤ) w, Int.cast_natCast]

  have heq : Submodule.ofFiniteIdele Λ (x * h) =
      Submodule.ofFiniteIdele Λ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x) := by
    rw [Submodule.ofFiniteIdele_diagonal_mul Λ δ x]
    ext z
    rw [Units.smul_def, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := hall z hz
      exact ⟨w, hw, by rw [← Units.smul_def, hδsmul]⟩
    · rintro ⟨w, hw, rfl⟩
      rw [← Units.smul_def, hδsmul]
      exact zsmul_mem_ofFiniteIdele_mul_of_mem_primeHeckeSet hΛ x hh hw
  have hst := (Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hΛ.fg hΛ.spanTop (x * h)
    (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x)).mp heq

  have hδA : ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) =
      algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) (ℓ : ℚ) := by
    rw [Submodule.val_finiteIdeleDiagonal_apply, hδval, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hcomm : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x = x * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ := by
    ext
    rw [Units.val_mul, Units.val_mul, hδA]
    exact Algebra.commutes _ _
  rw [hcomm, mul_inv_rev, mul_assoc, inv_mul_cancel_left] at hst

  have hmem := mem_finiteAdeleBox_of_mem_finiteIdeleStabilizer hΛ (inv_mem hst)
  rw [mul_inv_rev, inv_inv, Units.val_mul] at hmem
  apply hh.2.2.2
  have hinv : (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ)⁻¹ :
      (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) =
      algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) ((ℓ : ℚ)⁻¹) := by
    exact Units.inv_eq_of_mul_eq_one_right (by rw [hδA, ← map_mul, mul_inv_cancel₀ hℓQ, map_one])
  rw [hinv, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at hmem
  exact hmem

theorem star_mem_of_isOrder {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : IsOrder Λ₁) {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ₁) :
    star z ∈ Λ₁ := by
  obtain ⟨-, t, ht⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ₁ hz
  have h : star z = ((QuaternionAlgebra.trd z : ℚ) : ℍ[ℚ, a, b]) - z := by
    rw [← QuaternionAlgebra.add_star_eq_coe_trd z]; abel
  rw [h, ← ht]
  refine Submodule.sub_mem _ ?_ hz
  have : ((t : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]
  exact Submodule.smul_mem _ t hΛ₁.one_mem

theorem mul_mem_ofFiniteIdele {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : IsOrder Λ₁)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {z : ℍ[ℚ, a, b]}
    (hz : z ∈ Submodule.ofFiniteIdele Λ₁ g) {l : ℍ[ℚ, a, b]} (hl : l ∈ Λ₁) : z * l ∈ Submodule.ofFiniteIdele Λ₁ g := by
  rw [mem_ofFiniteIdele_iff'] at hz ⊢
  have e : (z * l) ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (z ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) * (l ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [e, ← mul_assoc]
  exact mul_mem_finiteAdeleBox hΛ₁ hz (tmul_mem_finiteAdeleBox hl fun v => one_mem _)

section N

variable {X₀ W : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic]
variable {θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]}
variable {χ : X₀.toAffine.Point →+ W.toAffine.Point} {d : (ℍ[ℚ, a, b])ˣ}
variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

def homsIntoSubgroup (hθ : Function.Injective θ) (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχs : Function.Surjective χ)
    (hχK : θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (J : Submodule ℤ ℍ[ℚ, a, b]) : AddSubgroup (W.toAffine.Point →+ X₀.toAffine.Point) where
  carrier := homsInto X₀ W θ χ d J
  zero_mem' := by
    refine (mem_homsInto_iff J 0).mpr ⟨WeierstrassCurve.zero_mem_rationalHomSet κ W X₀, compEnd hχ (WeierstrassCurve.zero_mem_rationalHomSet κ W X₀), rfl, ?_⟩
    have h0 : compEnd hχ (WeierstrassCurve.zero_mem_rationalHomSet κ W X₀) = 0 :=
      Subtype.ext (by rw [coe_compEnd]; ext P; rfl)
    rw [h0, map_zero]; exact J.zero_mem
  add_mem' := by
    intro ρ σ hρ hσ
    obtain ⟨hρ, e₁, he₁, h₁⟩ := (mem_homsInto_iff J ρ).mp hρ
    obtain ⟨hσ, e₂, he₂, h₂⟩ := (mem_homsInto_iff J σ).mp hσ
    refine (mem_homsInto_iff J _).mpr ⟨WeierstrassCurve.add_mem_rationalHomSet κ W X₀ hρ hσ, e₁ + e₂, ?_, ?_⟩
    · rw [Subring.coe_add, he₁, he₂]; exact (AddMonoidHom.add_comp ρ σ χ).symm
    · rw [map_add]; exact J.add_mem h₁ h₂
  neg_mem' := by
    intro ρ hρ
    obtain ⟨hρ, e, he, h⟩ := (mem_homsInto_iff J ρ).mp hρ
    refine (mem_homsInto_iff J _).mpr ⟨neg_mem_rationalHomSet_of_ker hθ hχ hχs hχK hρ, -e, ?_, ?_⟩
    · rw [Subring.coe_neg, he]; exact (AddMonoidHom.neg_comp ρ χ).symm
    · rw [map_neg]; exact J.neg_mem h

theorem comp_mem_homsInto (hΛ : IsOrder Λ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W)
    {J : Submodule ℤ ℍ[ℚ, a, b]} (hJmul : ∀ z ∈ J, ∀ l ∈ Λ, z * l ∈ J)
    {α : X₀.toAffine.Point →+ X₀.toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet κ X₀ X₀)
    {σ : W.toAffine.Point →+ X₀.toAffine.Point} (hσ : σ ∈ homsInto X₀ W θ χ d J) :
    α.comp σ ∈ homsInto X₀ W θ χ d J := by
  obtain ⟨hσ, e, he, hJ⟩ := (mem_homsInto_iff J σ).mp hσ
  have hασ : α.comp σ ∈ WeierstrassCurve.rationalHomSet κ W X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ W X₀ X₀ hσ hα
  let αe : ↥(WeierstrassCurve.rationalEndSubring κ X₀) := ⟨α, Subring.subset_closure hα⟩
  have hee : e = compEnd hχ hσ := eq_compEnd hχ hσ he
  have hmul : compEnd hχ hασ = αe * compEnd hχ hσ := Subtype.ext rfl
  have hαeΛ : θ αe ∈ Λ := by
    rw [← SetLike.mem_coe, ← hθΛ]; exact Set.mem_range_self αe
  have hstar : star (θ αe) ∈ Λ := star_mem_of_isOrder hΛ hαeΛ
  refine (mem_homsInto_iff J _).mpr ⟨hασ, compEnd hχ hασ, rfl, ?_⟩
  have : psi X₀ θ d (compEnd hχ hασ) = psi X₀ θ d (compEnd hχ hσ) * star (θ αe) := by
    rw [hmul, psi_apply, psi_apply, map_mul, star_mul, mul_assoc]
  rw [this, ← hee]
  exact hJmul _ hJ _ hstar

end N

end

end Ws3.StepDictBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet.Ws3 P2MW.S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet.Ws3.StepDictBody"
p2m_reactivate "P2MW.S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet.Ws3"

open Ws3.StepDictBody

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : (X₁.baseChange κ).toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (d : (ℍ[ℚ, a, b])ˣ) (r : ℕ) (hr : r.Prime) (hrq : r ≠ q')
    (y s : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hs : s ∈ primeHeckeSet Λ₁ r) :
    ∀ (W' : WeierstrassCurve κ) [W'.IsElliptic] (χ' : (X₁.baseChange κ).toAffine.Point →+ (W'.baseChange κ).toAffine.Point),
      χ' ∈ WeierstrassCurve.rationalHomSet κ X₁ W' → χ' ≠ 0 →
      θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' χ' =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ y : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) →
      ∃ C : AddSubgroup (W'.baseChange κ).toAffine.Point, (C : Set (W'.baseChange κ).toAffine.Point).Finite ∧ Nat.card C = r ∧
        θ₁ '' {e : ↥(WeierstrassCurve.rationalEndSubring κ X₁) | ∃ σ ∈ WeierstrassCurve.rationalHomSet κ W' X₁,
            (∀ P ∈ C, σ P = 0) ∧ (e : AddMonoid.End (X₁.baseChange κ).toAffine.Point) = σ.comp χ'} =
          star '' ((d • Submodule.ofFiniteIdele Λ₁ (y * s) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  intro W' _ χ' hχ' hχ'0 hK
  have hΛo : IsOrder Λ₁ := hΛ₁.isOrder
  have hrκ : (r : κ) ≠ 0 := by
    intro h
    exact hrq ((Nat.prime_dvd_prime_iff_eq Fact.out hr).mp ((CharP.cast_eq_zero_iff κ q' r).mp h)).symm

  have hJI : Submodule.ofFiniteIdele Λ₁ (y * s) ≤ Submodule.ofFiniteIdele Λ₁ y := ofFiniteIdele_mul_le_of_mem_primeHeckeSet hΛo y hs
  have hrI : ∀ z ∈ Submodule.ofFiniteIdele Λ₁ y, (r : ℤ) • z ∈ Submodule.ofFiniteIdele Λ₁ (y * s) :=
    fun z hz => zsmul_mem_ofFiniteIdele_mul_of_mem_primeHeckeSet hΛo y hs hz
  have hJne : Submodule.ofFiniteIdele Λ₁ (y * s) ≠ Submodule.ofFiniteIdele Λ₁ y := ofFiniteIdele_mul_ne_of_mem_primeHeckeSet hΛo y hs
  have hJdiv := not_forall_mem_ofFiniteIdele_mul_exists_eq_smul hΛo y hr.ne_zero hs
  have hJmul : ∀ z ∈ Submodule.ofFiniteIdele Λ₁ (y * s), ∀ l ∈ Λ₁, z * l ∈ Submodule.ofFiniteIdele Λ₁ (y * s) :=
    fun z hz l hl => mul_mem_ofFiniteIdele hΛo _ hz hl
  have hχ's : Function.Surjective χ' := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ' hχ'0
  set J := Submodule.ofFiniteIdele Λ₁ (y * s) with hJdef

  let S : AddSubmonoid ((W'.baseChange κ).toAffine.Point →+ (X₁.baseChange κ).toAffine.Point) :=
    { carrier := {ρ | ρ ∈ WeierstrassCurve.rationalHomSet κ W' X₁}
      zero_mem' := WeierstrassCurve.zero_mem_rationalHomSet κ W' X₁
      add_mem' := fun hρ hσ => WeierstrassCurve.add_mem_rationalHomSet κ W' X₁ hρ hσ }

  let M : AddSubgroup ((W'.baseChange κ).toAffine.Point →+ (X₁.baseChange κ).toAffine.Point) :=
    homsIntoSubgroup (X₀ := X₁) (W := W') hθ₁ hχ' hχ's hK J
  have hMiff : ∀ ρ : (W'.baseChange κ).toAffine.Point →+ (X₁.baseChange κ).toAffine.Point,
      ρ ∈ M ↔ ρ ∈ WeierstrassCurve.rationalHomSet κ W' X₁ ∧
        ∃ e : ↥(WeierstrassCurve.rationalEndSubring κ X₁),
          (e : AddMonoid.End (X₁.baseChange κ).toAffine.Point) = ρ.comp χ' ∧ psi X₁ θ₁ d e ∈ J :=
    fun ρ => mem_homsInto_iff (X₀ := X₁) (W := W') (θ := θ₁) (χ := χ') (d := d) J ρ

  have hMiff' : ∀ {ρ : (W'.baseChange κ).toAffine.Point →+ (X₁.baseChange κ).toAffine.Point}
      (hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ W' X₁), ρ ∈ M ↔ psi X₁ θ₁ d (compEnd hχ' hρ) ∈ J := by
    intro ρ hρ
    rw [hMiff]
    constructor
    · rintro ⟨-, e, he, hJ⟩
      rwa [eq_compEnd hχ' hρ he] at hJ
    · intro h
      exact ⟨hρ, compEnd hχ' hρ, rfl, h⟩
  have hMsub : (M : Set _) ⊆ WeierstrassCurve.rationalHomSet κ W' X₁ := fun ρ hρ => ((hMiff ρ).mp hρ).1

  have hMr : ∀ ρ ∈ WeierstrassCurve.rationalHomSet κ W' X₁, r • ρ ∈ M := by
    intro ρ hρ
    have hrρ : r • ρ ∈ WeierstrassCurve.rationalHomSet κ W' X₁ := S.nsmul_mem (show ρ ∈ S from hρ) r
    rw [hMiff' hrρ]
    have he : compEnd hχ' hrρ = r • compEnd hχ' hρ := by
      apply Subtype.ext
      rw [coe_compEnd, AddSubmonoidClass.coe_nsmul, coe_compEnd]
      ext P
      rfl
    rw [he, map_nsmul, ← natCast_zsmul]
    exact hrI _ (psi_compEnd_mem hχ' hK hρ)

  have hMst : ∀ α ∈ WeierstrassCurve.rationalHomSet κ X₁ X₁, ∀ ρ ∈ M, α.comp ρ ∈ M :=
    fun α hα ρ hρ => comp_mem_homsInto (X₀ := X₁) (W := W') hΛo hθ₁Λ hχ' hJmul hα hρ

  let C : AddSubgroup (W'.baseChange κ).toAffine.Point :=
    { carrier := {P | (r : ℤ) • P = 0 ∧ ∀ μ ∈ M, μ P = 0}
      zero_mem' := ⟨smul_zero _, fun μ _ => map_zero μ⟩
      add_mem' := fun {P Q} hP hQ =>
        ⟨by rw [smul_add, hP.1, hQ.1, add_zero], fun μ hμ => by rw [map_add, hP.2 μ hμ, hQ.2 μ hμ, add_zero]⟩
      neg_mem' := fun {P} hP => ⟨by rw [smul_neg, hP.1, neg_zero], fun μ hμ => by rw [map_neg, hP.2 μ hμ, neg_zero]⟩ }
  have hmemC : ∀ P, P ∈ C ↔ (r : ℤ) • P = 0 ∧ ∀ μ ∈ M, μ P = 0 := fun P => Iff.rfl

  have hW' : ∃ σ ∈ WeierstrassCurve.rationalHomSet κ W' X₁, σ ≠ 0 := by
    obtain ⟨σ, hσ, n, hn, hd⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₁ W' hχ' hχ'0
    refine ⟨σ, hσ, fun h0 => ?_⟩
    obtain ⟨p, hpge, hpp⟩ := Nat.exists_infinite_primes (max n.toNat q' + 1)
    have hpq : p ≠ q' := by omega
    have hpκ : (p : κ) ≠ 0 := by
      intro h
      exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out hpp).mp ((CharP.cast_eq_zero_iff κ q' p).mp h)).symm
    obtain ⟨R, hR⟩ : ∃ R : (X₁.baseChange κ).toAffine.Point, addOrderOf R = p :=
      WeierstrassCurve.exists_addOrderOf_eq_prime_of_isAlgClosed X₁ p hpp hpκ
    have h1 : n • R = 0 := by rw [← hd.comp_left R, h0, AddMonoidHom.zero_apply]
    have h2 : ((addOrderOf R : ℕ) : ℤ) ∣ n := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
    rw [hR] at h2
    have h3 : (p : ℤ) ≤ n := Int.le_of_dvd hn h2
    omega

  have hdict := (WeierstrassCurve.relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero
    X₁ a b Λ₁ hΛo θ₁ hθ₁ hθ₁Λ W' hW' r hr hrκ).2 M hMsub hMr hMst
  have hAnn : ∀ σ ∈ WeierstrassCurve.rationalHomSet κ W' X₁, (∀ P ∈ C, σ P = 0) ↔ σ ∈ M := by
    intro σ hσ
    constructor
    · intro h
      exact hdict σ hσ (fun P hP hPM => h P ⟨hP, hPM⟩)
    · intro hσM P hP
      exact hP.2 σ hσM

  have hCle : ∀ P ∈ C, P ∈ Submodule.torsionBy ℤ (W'.baseChange κ).toAffine.Point (r : ℤ) := fun P hP =>
    (Submodule.mem_torsionBy_iff _ _).mpr hP.1
  have hcardT : Nat.card (Submodule.torsionBy ℤ (W'.baseChange κ).toAffine.Point (r : ℤ)) = r ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W' hrκ
  haveI hfinT : Finite (Submodule.torsionBy ℤ (W'.baseChange κ).toAffine.Point (r : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; exact pow_ne_zero 2 hr.ne_zero)
  have hCT : C.toIntSubmodule ≤ Submodule.torsionBy ℤ (W'.baseChange κ).toAffine.Point (r : ℤ) := fun P hP => hCle P hP
  haveI hfinC : Finite C := Finite.of_injective (Submodule.inclusion hCT) (Submodule.inclusion_injective hCT)
  have hCfin : (C : Set (W'.baseChange κ).toAffine.Point).Finite := Set.toFinite _

  have hCT' : C ≤ (Submodule.torsionBy ℤ (W'.baseChange κ).toAffine.Point (r : ℤ)).toAddSubgroup := fun P hP => hCle P hP
  have hdvd : Nat.card C ∣ r ^ 2 := by
    rw [← hcardT]
    exact AddSubgroup.card_dvd_of_le hCT'

  obtain ⟨i, hi2, hci⟩ := (Nat.dvd_prime_pow hr).mp hdvd
  have hI_of_M : ∀ {σ : (W'.baseChange κ).toAffine.Point →+ (X₁.baseChange κ).toAffine.Point}
      (hσ : σ ∈ WeierstrassCurve.rationalHomSet κ W' X₁), psi X₁ θ₁ d (compEnd hχ' hσ) ∈ Submodule.ofFiniteIdele Λ₁ y :=
    fun hσ => psi_compEnd_mem hχ' hK hσ
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hci
    apply hJne
    refine le_antisymm hJI (fun z hz => ?_)
    obtain ⟨σ, hσ, hσz⟩ : ∃ σ : (W'.baseChange κ).toAffine.Point →+ (X₁.baseChange κ).toAffine.Point,
        ∃ hσ : σ ∈ WeierstrassCurve.rationalHomSet κ W' X₁, psi X₁ θ₁ d (compEnd hχ' hσ) = z :=
      exists_psi_compEnd_eq hχ' hK hz

    haveI : Subsingleton C := (Nat.card_eq_one_iff_unique.mp hci).1
    have hkill : ∀ P ∈ C, σ P = 0 := by
      intro P hP
      have : (⟨P, hP⟩ : C) = ⟨0, C.zero_mem⟩ := Subsingleton.elim _ _
      rw [show P = 0 from congrArg Subtype.val this, map_zero]
    have hσM : σ ∈ M := (hAnn σ hσ).mp hkill
    rw [← hσz]
    exact (hMiff' hσ).mp hσM
  have hi2' : i ≠ 2 := by
    rintro rfl

    have hCeq : C = (Submodule.torsionBy ℤ (W'.baseChange κ).toAffine.Point (r : ℤ)).toAddSubgroup :=
      AddSubgroup.eq_of_le_of_card_ge hCT' (by rw [hci]; exact hcardT.le)
    apply hJdiv
    intro z hz
    obtain ⟨σ, hσ, hσz⟩ : ∃ σ : (W'.baseChange κ).toAffine.Point →+ (X₁.baseChange κ).toAffine.Point,
        ∃ hσ : σ ∈ WeierstrassCurve.rationalHomSet κ W' X₁, psi X₁ θ₁ d (compEnd hχ' hσ) = z :=
      exists_psi_compEnd_eq hχ' hK (hJI hz)
    have hσM : σ ∈ M := (hMiff' hσ).mpr (hσz ▸ hz)

    have hker : ∀ P : (W'.baseChange κ).toAffine.Point, (r : ℤ) • P = 0 → σ P = 0 := by
      intro P hP
      have hPC : P ∈ C := by
        rw [hCeq]
        exact (Submodule.mem_torsionBy_iff _ _).mpr hP
      exact hPC.2 σ hσM
    obtain ⟨β, hβ, hσβ⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W' X₁ hrκ hσ hker
    refine ⟨psi X₁ θ₁ d (compEnd hχ' hβ), hI_of_M hβ, ?_⟩
    have he : compEnd hχ' hσ = r • compEnd hχ' hβ := by
      apply Subtype.ext
      rw [coe_compEnd, AddSubmonoidClass.coe_nsmul, coe_compEnd]
      ext P
      show σ (χ' P) = _
      rw [hσβ, ← natCast_zsmul]
      rfl
    rw [← hσz, he, map_nsmul, natCast_zsmul]
  have hi1 : i = 1 := by omega
  subst hi1
  rw [pow_one] at hci

  refine ⟨C, hCfin, hci, ?_⟩
  ext w
  constructor
  · rintro ⟨e, ⟨σ, hσ, hσC, he⟩, rfl⟩
    have hσM : σ ∈ M := (hAnn σ hσ).mp hσC
    have hJmem := (hMiff' hσ).mp hσM
    rw [← eq_compEnd hχ' hσ he, psi_apply] at hJmem
    exact (mem_star_image_smul_iff J (θ₁ e)).mpr hJmem
  · intro hw
    have hw' := (mem_star_image_smul_iff J w).mp hw
    obtain ⟨σ, hσ, hσw⟩ : ∃ σ : (W'.baseChange κ).toAffine.Point →+ (X₁.baseChange κ).toAffine.Point,
        ∃ hσ : σ ∈ WeierstrassCurve.rationalHomSet κ W' X₁,
          psi X₁ θ₁ d (compEnd hχ' hσ) = ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star w :=
      exists_psi_compEnd_eq hχ' hK (hJI hw')
    have hσM : σ ∈ M := (hMiff' hσ).mpr (hσw ▸ hw')
    refine ⟨compEnd hχ' hσ, ⟨σ, hσ, (hAnn σ hσ).mpr hσM, rfl⟩, ?_⟩
    have h1 : psi X₁ θ₁ d (compEnd hχ' hσ) = ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * star w := hσw
    rw [psi_apply] at h1
    exact star_injective ((Units.mul_right_inj _).mp h1)

end S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet
end P2MW
export P2MW.S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet (solution)
