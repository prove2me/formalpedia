-- Prove2me | solution 1 for GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8f687cfc-ea0f-52ac-b9bb-e75d0794dbba

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_GaloisRepAdic_isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt
import Theorems.Thm_groupCohomology_finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal
import Theorems.Thm_FreyPackage_exists_inertia_cycloPinned_ne_one_v2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation Module

noncomputable section

namespace P2mBpStr

variable {k : Type} [Field k]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Coordinates

variable (ρbar : ResidualGaloisRep k) (ρA : GaloisRepAdic (DualNumber k))
  (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V)

def π₀ (v : ρA.V) : ρbar.V := ∑ i, (b.repr v i).fst • bbar i

def π₁ (v : ρA.V) : ρbar.V := ∑ i, (b.repr v i).snd • bbar i

lemma π₀_add (v w : ρA.V) : π₀ ρbar ρA b bbar (v + w) = π₀ ρbar ρA b bbar v + π₀ ρbar ρA b bbar w := by
  simp only [π₀, map_add, Finsupp.add_apply, fst_add, add_smul, Finset.sum_add_distrib]

lemma π₁_add (v w : ρA.V) : π₁ ρbar ρA b bbar (v + w) = π₁ ρbar ρA b bbar v + π₁ ρbar ρA b bbar w := by
  simp only [π₁, map_add, Finsupp.add_apply, snd_add, add_smul, Finset.sum_add_distrib]

lemma π₀_smul (a : DualNumber k) (v : ρA.V) :
    π₀ ρbar ρA b bbar (a • v) = a.fst • π₀ ρbar ρA b bbar v := by
  simp only [π₀, map_smul, Finsupp.smul_apply, smul_eq_mul, fst_mul, Finset.smul_sum, smul_smul]

lemma π₁_smul (a : DualNumber k) (v : ρA.V) :
    π₁ ρbar ρA b bbar (a • v) = a.fst • π₁ ρbar ρA b bbar v + a.snd • π₀ ρbar ρA b bbar v := by
  simp only [π₁, π₀, map_smul, Finsupp.smul_apply, smul_eq_mul, snd_mul, Finset.smul_sum, smul_smul,
    ← Finset.sum_add_distrib, ← add_smul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

lemma π₀_zero : π₀ ρbar ρA b bbar 0 = 0 := by simp [π₀]

lemma π₁_zero : π₁ ρbar ρA b bbar 0 = 0 := by simp [π₁]

lemma π₀_neg (v : ρA.V) : π₀ ρbar ρA b bbar (-v) = -π₀ ρbar ρA b bbar v := by
  simp only [π₀, map_neg, Finsupp.neg_apply, fst_neg, neg_smul, Finset.sum_neg_distrib]

lemma π₀_sub (v w : ρA.V) : π₀ ρbar ρA b bbar (v - w) = π₀ ρbar ρA b bbar v - π₀ ρbar ρA b bbar w := by
  rw [sub_eq_add_neg, π₀_add, π₀_neg, sub_eq_add_neg]

lemma π₀_basis (j : Fin 2) : π₀ ρbar ρA b bbar (b j) = bbar j := by
  simp only [π₀, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Finsupp.single_eq_of_ne hij]
  · simp

lemma π₁_basis (j : Fin 2) : π₁ ρbar ρA b bbar (b j) = 0 := by
  simp only [π₁, Module.Basis.repr_self]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [Finsupp.single_eq_of_ne hij]

lemma repr_π₀ (v : ρA.V) (i : Fin 2) : bbar.repr (π₀ ρbar ρA b bbar v) i = (b.repr v i).fst := by
  simp only [π₀, map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finset.sum_apply']
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma repr_π₁ (v : ρA.V) (i : Fin 2) : bbar.repr (π₁ ρbar ρA b bbar v) i = (b.repr v i).snd := by
  simp only [π₁, map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finset.sum_apply']
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma eq_of_π_eq {v w : ρA.V} (h0 : π₀ ρbar ρA b bbar v = π₀ ρbar ρA b bbar w)
    (h1 : π₁ ρbar ρA b bbar v = π₁ ρbar ρA b bbar w) : v = w := by
  apply b.repr.injective
  ext i
  · rw [← repr_π₀ ρbar ρA b bbar v i, ← repr_π₀ ρbar ρA b bbar w i, h0]
  · rw [← repr_π₁ ρbar ρA b bbar v i, ← repr_π₁ ρbar ρA b bbar w i, h1]

lemma π_eps_smul (v : ρA.V) :
    π₀ ρbar ρA b bbar ((DualNumber.eps : DualNumber k) • v) = 0 ∧
      π₁ ρbar ρA b bbar ((DualNumber.eps : DualNumber k) • v) = π₀ ρbar ρA b bbar v := by
  refine ⟨?_, ?_⟩
  · rw [π₀_smul, DualNumber.fst_eps, zero_smul]
  · rw [π₁_smul, DualNumber.fst_eps, DualNumber.snd_eps, zero_smul, one_smul, zero_add]

def lift (v₀ v₁ : ρbar.V) : ρA.V :=
  ∑ i, (TrivSqZeroExt.inl (bbar.repr v₀ i) + TrivSqZeroExt.inr (bbar.repr v₁ i)) • b i

lemma π₀_lift (v₀ v₁ : ρbar.V) : π₀ ρbar ρA b bbar (lift ρbar ρA b bbar v₀ v₁) = v₀ := by
  apply bbar.repr.injective; ext i
  rw [repr_π₀]
  simp only [lift, map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finset.sum_apply']
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma π₁_lift (v₀ v₁ : ρbar.V) : π₁ ρbar ρA b bbar (lift ρbar ρA b bbar v₀ v₁) = v₁ := by
  apply bbar.repr.injective; ext i
  rw [repr_π₁]
  simp only [lift, map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finset.sum_apply']
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro h; exact absurd (Finset.mem_univ i) h

variable (ρd : Γℚ →* (DualNumber (Module.End k ρbar.V))ˣ)
  (hfr : ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩)

include hfr

lemma π₀_ρA_basis (σ : Γℚ) (j : Fin 2) :
    π₀ ρbar ρA b bbar (ρA.ρ σ (b j)) = ((ρd σ : DualNumber (Module.End k ρbar.V)).fst) (bbar j) := by
  apply bbar.repr.injective; ext i
  rw [repr_π₀, ← LinearMap.toMatrix_apply, hfr σ, ← LinearMap.toMatrix_apply bbar bbar]
  simp [Matrix.dualNumberEquiv]

lemma π₁_ρA_basis (σ : Γℚ) (j : Fin 2) :
    π₁ ρbar ρA b bbar (ρA.ρ σ (b j)) = ((ρd σ : DualNumber (Module.End k ρbar.V)).snd) (bbar j) := by
  apply bbar.repr.injective; ext i
  rw [repr_π₁, ← LinearMap.toMatrix_apply, hfr σ, ← LinearMap.toMatrix_apply bbar bbar]
  simp [Matrix.dualNumberEquiv]

lemma π₀_ρA (σ : Γℚ) (v : ρA.V) :
    π₀ ρbar ρA b bbar (ρA.ρ σ v) = ((ρd σ : DualNumber (Module.End k ρbar.V)).fst) (π₀ ρbar ρA b bbar v) := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  have : ∀ j, π₀ ρbar ρA b bbar (ρA.ρ σ (b.repr v j • b j)) =
      (b.repr v j).fst • ((ρd σ : DualNumber (Module.End k ρbar.V)).fst) (bbar j) := by
    intro j
    rw [LinearMap.map_smul, π₀_smul, π₀_ρA_basis ρbar ρA b bbar ρd hfr]
  rw [show π₀ ρbar ρA b bbar (∑ j, ρA.ρ σ (b.repr v j • b j)) =
      ∑ j, π₀ ρbar ρA b bbar (ρA.ρ σ (b.repr v j • b j)) from
    map_sum (⟨⟨π₀ ρbar ρA b bbar, π₀_zero ρbar ρA b bbar⟩, π₀_add ρbar ρA b bbar⟩ : ρA.V →+ ρbar.V) _ _]
  simp_rw [this]
  rw [show π₀ ρbar ρA b bbar v = ∑ i, (b.repr v i).fst • bbar i from rfl, map_sum]
  simp_rw [map_smul]

lemma π₁_ρA (σ : Γℚ) (v : ρA.V) :
    π₁ ρbar ρA b bbar (ρA.ρ σ v) =
      ((ρd σ : DualNumber (Module.End k ρbar.V)).fst) (π₁ ρbar ρA b bbar v) +
        ((ρd σ : DualNumber (Module.End k ρbar.V)).snd) (π₀ ρbar ρA b bbar v) := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  have : ∀ j, π₁ ρbar ρA b bbar (ρA.ρ σ (b.repr v j • b j)) =
      (b.repr v j).fst • ((ρd σ : DualNumber (Module.End k ρbar.V)).snd) (bbar j) +
        (b.repr v j).snd • ((ρd σ : DualNumber (Module.End k ρbar.V)).fst) (bbar j) := by
    intro j
    rw [LinearMap.map_smul, π₁_smul, π₀_ρA_basis ρbar ρA b bbar ρd hfr, π₁_ρA_basis ρbar ρA b bbar ρd hfr]
  rw [show π₁ ρbar ρA b bbar (∑ j, ρA.ρ σ (b.repr v j • b j)) =
      ∑ j, π₁ ρbar ρA b bbar (ρA.ρ σ (b.repr v j • b j)) from
    map_sum (⟨⟨π₁ ρbar ρA b bbar, π₁_zero ρbar ρA b bbar⟩, π₁_add ρbar ρA b bbar⟩ : ρA.V →+ ρbar.V) _ _]
  simp_rw [this, Finset.sum_add_distrib]
  rw [show π₀ ρbar ρA b bbar v = ∑ i, (b.repr v i).fst • bbar i from rfl,
    show π₁ ρbar ρA b bbar v = ∑ i, (b.repr v i).snd • bbar i from rfl, map_sum, map_sum]
  simp_rw [map_smul]
  rw [add_comm]

end Coordinates

section Strict

variable (ρbar : ResidualGaloisRep k) (ρA : GaloisRepAdic (DualNumber k))
  (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V)
  (ρd : Γℚ →* (DualNumber (Module.End k ρbar.V))ˣ)
  (hd : IsDualLift ρbar.ρ.toHomUnits ρd)
  (hfr : ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩)
  (c : cocycles₁ ρbar.adZero)
  (hc : ∀ σ, ((c : Γℚ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρd σ)

local notation "V̄" => ρbar.V

def cE (σ : Γℚ) : Module.End k ρbar.V :=
  (((c : Γℚ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ :
    ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) : Module.End k ρbar.V)

lemma cE_def (σ : Γℚ) : cE ρbar c σ =
    (((c : Γℚ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ :
      ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) : Module.End k ρbar.V) := rfl

lemma trace_cE (σ : Γℚ) : LinearMap.trace k ρbar.V (cE ρbar c σ) = 0 :=
  ((c : Γℚ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ).2

include hd in
lemma fst_ρd (σ : Γℚ) : ((ρd σ : DualNumber (Module.End k ρbar.V)).fst) = ρbar.ρ σ := hd σ

include hc in
lemma snd_ρd (σ : Γℚ) : ((ρd σ : DualNumber (Module.End k ρbar.V)).snd) = (cE ρbar c σ) * ρbar.ρ σ := by
  rw [cE_def, hc σ]
  unfold dualLiftToCochain
  have h1 : ((ρbar.ρ.toHomUnits σ)⁻¹ : (Module.End k ρbar.V)ˣ).val * ρbar.ρ σ = 1 := by
    rw [← MonoidHom.coe_toHomUnits ρbar.ρ σ]
    exact Units.inv_mul _
  rw [mul_assoc, h1, mul_one]

lemma ρbar_inv_mul (σ : Γℚ) : ρbar.ρ σ⁻¹ * ρbar.ρ σ = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

lemma ρbar_mul_inv (σ : Γℚ) : ρbar.ρ σ * ρbar.ρ σ⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

lemma ρbar_injective (σ : Γℚ) : Function.Injective (ρbar.ρ σ) := by
  intro v w h
  have := congrArg (ρbar.ρ σ⁻¹) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ρbar_inv_mul, Module.End.one_apply,
    Module.End.one_apply] at this

include hd hfr in
lemma π₀_ρA' (σ : Γℚ) (v : ρA.V) :
    π₀ ρbar ρA b bbar (ρA.ρ σ v) = ρbar.ρ σ (π₀ ρbar ρA b bbar v) := by
  rw [π₀_ρA ρbar ρA b bbar ρd hfr, fst_ρd ρbar ρd hd]

include hd hfr hc in
lemma π₁_ρA' (σ : Γℚ) (v : ρA.V) :
    π₁ ρbar ρA b bbar (ρA.ρ σ v) =
      ρbar.ρ σ (π₁ ρbar ρA b bbar v) + (cE ρbar c σ) (ρbar.ρ σ (π₀ ρbar ρA b bbar v)) := by
  rw [π₁_ρA ρbar ρA b bbar ρd hfr, fst_ρd ρbar ρd hd, snd_ρd ρbar ρd c hc, Module.End.mul_apply]

def π₁' (X : Module.End k V̄) (u : ρA.V) : V̄ := π₁ ρbar ρA b bbar u - X (π₀ ρbar ρA b bbar u)

def c' (X : Module.End k V̄) (σ : Γℚ) : Module.End k V̄ :=
  (cE ρbar c σ) + (ρbar.ρ σ * X * ρbar.ρ σ⁻¹ - X)

lemma π₁'_smul (X : Module.End k V̄) (a : DualNumber k) (u : ρA.V) :
    π₁' ρbar ρA b bbar X (a • u) = a.fst • π₁' ρbar ρA b bbar X u + a.snd • π₀ ρbar ρA b bbar u := by
  simp only [π₁', π₁_smul, π₀_smul, map_smul, smul_sub]
  abel

include hd hfr hc in
lemma π₁'_ρA (X : Module.End k V̄) (σ : Γℚ) (u : ρA.V) :
    π₁' ρbar ρA b bbar X (ρA.ρ σ u) =
      ρbar.ρ σ (π₁' ρbar ρA b bbar X u) + c' ρbar c X σ (ρbar.ρ σ (π₀ ρbar ρA b bbar u)) := by
  simp only [π₁', c', π₁_ρA' ρbar ρA b bbar ρd hd hfr c hc, π₀_ρA' ρbar ρA b bbar ρd hd hfr,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, map_sub]
  rw [← Module.End.mul_apply (ρbar.ρ σ⁻¹) (ρbar.ρ σ), ρbar_inv_mul, Module.End.one_apply]
  abel

lemma parts_mem_of_mem_span (X : Module.End k V̄) (w : ρA.V)
    (hX : X (π₀ ρbar ρA b bbar w) = π₁ ρbar ρA b bbar w) {u : ρA.V}
    (hu : u ∈ (DualNumber k) ∙ w) :
    π₀ ρbar ρA b bbar u ∈ k ∙ π₀ ρbar ρA b bbar w ∧
      π₁' ρbar ρA b bbar X u ∈ k ∙ π₀ ρbar ρA b bbar w := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
  refine ⟨?_, ?_⟩
  · rw [π₀_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [π₁'_smul]
    have : π₁' ρbar ρA b bbar X w = 0 := by rw [π₁', hX, sub_self]
    rw [this, smul_zero, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

lemma π₀_basis_ne_zero (b' : Module.Basis (Fin 2) (DualNumber k) ρA.V) (i : Fin 2) :
    π₀ ρbar ρA b bbar (b' i) ≠ 0 := by
  intro h0

  set u := lift ρbar ρA b bbar (π₁ ρbar ρA b bbar (b' i)) 0 with hu
  have hεu : (DualNumber.eps : DualNumber k) • u = b' i := by
    apply eq_of_π_eq ρbar ρA b bbar
    · rw [(π_eps_smul ρbar ρA b bbar u).1, h0]
    · rw [(π_eps_smul ρbar ρA b bbar u).2, hu, π₀_lift]
  have hε2 : (DualNumber.eps : DualNumber k) • b' i = 0 := by
    rw [← hεu, smul_smul, DualNumber.eps_mul_eps, zero_smul]
  have := congrArg (fun v => b'.repr v i) hε2
  simp only [map_smul, map_zero, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, Finsupp.coe_zero, Pi.zero_apply] at this
  have h1 := congrArg TrivSqZeroExt.snd this
  rw [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] at h1
  exact one_ne_zero h1

lemma exists_pow_action (p : ℕ) [Fact p.Prime] (σ : Γℚ) :
    ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ 1 = 1 → σ μ = μ ^ a := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.2 hp⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hσζ : (σ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζ
  refine ⟨a, fun μ hμ => ?_⟩
  rw [pow_one] at hμ
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]

include hd hfr hc in

theorem exists_resStrict (p : ℕ) [Fact p.Prime] [CharP k p] (h2 : (2 : k) ≠ 0)
    (hstr : ρA.IsStrictOrdinaryAt p) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ (w₀ : V̄) (X : Module.End k V̄), w₀ ≠ 0 ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ρbar.ρ σ w₀ ∈ k ∙ w₀) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : V̄, ρbar.ρ σ v - v ∈ k ∙ w₀) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∃ x z : k,
        ρbar.ρ σ w₀ = x • w₀ ∧ (∀ v : V̄, ρbar.ρ σ v - z • v ∈ k ∙ w₀) ∧
        ∀ (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
          x - (a : k) * z ∈ Ideal.span {((p ^ n : ℕ) : k)}) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ,
        (∀ v : V̄, c' ρbar c X σ v ∈ k ∙ w₀) ∧ c' ρbar c X σ w₀ = 0) := by
  obtain ⟨-, hplaces⟩ := hstr
  obtain ⟨L, ⟨b', hL⟩, hstab, hinert, hsc⟩ := hplaces P hP
  set w := b' 0 with hwdef
  set w₀ := π₀ ρbar ρA b bbar w with hw₀
  set w₁ := π₁ ρbar ρA b bbar w with hw₁
  have hw₀ne : w₀ ≠ 0 := π₀_basis_ne_zero ρbar ρA b bbar b' 0

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton k V̄ w₀)
    (LinearMap.ker_toSpanSingleton k hw₀ne)
  set X : Module.End k V̄ := g.smulRight w₁ with hXdef
  have hXw : X w₀ = w₁ := by
    have := LinearMap.congr_fun hg (1 : k)
    simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.id_apply] at this
    rw [hXdef, LinearMap.smulRight_apply, this, one_smul]
  have hwL : w ∈ L := by rw [hL]; exact Submodule.mem_span_singleton_self _
  have hmemL : ∀ {u : ρA.V}, u ∈ L → π₀ ρbar ρA b bbar u ∈ k ∙ w₀ ∧ π₁' ρbar ρA b bbar X u ∈ k ∙ w₀ := by
    intro u hu
    rw [hL] at hu
    exact parts_mem_of_mem_span ρbar ρA b bbar X w hXw hu
  have hπ₁'w : π₁' ρbar ρA b bbar X w = 0 := by rw [π₁', hXw, sub_self]

  have hres_stab : ∀ σ ∈ P.decompositionSubgroup ℚ, ρbar.ρ σ w₀ ∈ k ∙ w₀ := by
    intro σ hσ
    have := (hmemL (hstab σ hσ w hwL)).1
    rwa [π₀_ρA' ρbar ρA b bbar ρd hd hfr] at this
  have hres_inert : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : V̄, ρbar.ρ σ v - v ∈ k ∙ w₀ := by
    intro σ hσ v
    have := (hmemL (hinert σ hσ (lift ρbar ρA b bbar v 0))).1
    rwa [π₀_sub, π₀_ρA' ρbar ρA b bbar ρd hd hfr, π₀_lift] at this
  refine ⟨w₀, X, hw₀ne, hres_stab, hres_inert, ?_, ?_⟩
  ·
    intro σ hσ
    obtain ⟨x, z, hx, hz, hxz⟩ := hsc σ hσ
    refine ⟨x.fst, z.fst, ?_, fun v => ?_, fun n a ha => ?_⟩
    · have := congrArg (π₀ ρbar ρA b bbar) (hx w hwL)
      rwa [π₀_ρA' ρbar ρA b bbar ρd hd hfr, π₀_smul] at this
    · have := (hmemL (hz (lift ρbar ρA b bbar v 0))).1
      rwa [π₀_sub, π₀_ρA' ρbar ρA b bbar ρd hd hfr, π₀_smul, π₀_lift] at this
    · obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hxz n a ha)
      refine Ideal.mem_span_singleton'.2 ⟨r.fst, ?_⟩
      have := congrArg TrivSqZeroExt.fst hr
      rw [fst_mul, fst_sub, fst_mul, fst_natCast, fst_natCast] at this
      exact this
  ·
    intro σ hσ
    obtain ⟨x, z, hx, hz, hxz⟩ := hsc σ hσ
    obtain ⟨a, ha⟩ := exists_pow_action p σ

    have hxaz : x = (a : DualNumber k) * z := by
      have h := hxz 1 a ha
      rw [pow_one, show ((p : ℕ) : DualNumber k) = 0 from by
        rw [← map_natCast (algebraMap k (DualNumber k)) p, CharP.cast_eq_zero, map_zero],
        Ideal.span_singleton_zero, Ideal.mem_bot, sub_eq_zero] at h
      exact h

    have hx0 : ρbar.ρ σ w₀ = x.fst • w₀ := by
      have := congrArg (π₀ ρbar ρA b bbar) (hx w hwL)
      rwa [π₀_ρA' ρbar ρA b bbar ρd hd hfr, π₀_smul] at this
    have hx0ne : x.fst ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hx0
      exact hw₀ne (ρbar_injective ρbar σ (by rw [hx0, map_zero]))
    have hz0 : ∀ v : V̄, ρbar.ρ σ v - z.fst • v ∈ k ∙ w₀ := by
      intro v
      have := (hmemL (hz (lift ρbar ρA b bbar v 0))).1
      rwa [π₀_sub, π₀_ρA' ρbar ρA b bbar ρd hd hfr, π₀_smul, π₀_lift] at this
    have hxz0 : x.fst = (a : k) * z.fst := by
      have := congrArg TrivSqZeroExt.fst hxaz; rwa [fst_mul, fst_natCast] at this
    have hxz1 : x.snd = (a : k) * z.snd := by
      have := congrArg TrivSqZeroExt.snd hxaz
      rw [snd_mul, snd_natCast, fst_natCast] at this
      simpa using this
    have hane : (a : k) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hxz0; exact hx0ne hxz0
    have hz0ne : z.fst ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hxz0; exact hx0ne hxz0

    have hcw : x.fst • c' ρbar c X σ w₀ = x.snd • w₀ := by
      have h1 := congrArg (π₁' ρbar ρA b bbar X) (hx w hwL)
      rw [π₁'_ρA ρbar ρA b bbar ρd hd hfr c hc, hπ₁'w, map_zero, zero_add, π₁'_smul, hπ₁'w,
        smul_zero, zero_add, hx0, map_smul] at h1
      exact h1

    have hcz : ∀ v : V̄, c' ρbar c X σ (ρbar.ρ σ v) - z.snd • v ∈ k ∙ w₀ := by
      intro v
      have h1 := (hmemL (hz (lift ρbar ρA b bbar v (X v)))).2
      have hπ' : π₁' ρbar ρA b bbar X (lift ρbar ρA b bbar v (X v)) = 0 := by
        rw [π₁', π₁_lift, π₀_lift, sub_self]
      rw [show ρA.ρ σ (lift ρbar ρA b bbar v (X v)) - z • lift ρbar ρA b bbar v (X v) =
          ρA.ρ σ (lift ρbar ρA b bbar v (X v)) + (-z) • lift ρbar ρA b bbar v (X v) from by
          rw [neg_smul, sub_eq_add_neg]] at h1
      rw [show π₁' ρbar ρA b bbar X (ρA.ρ σ (lift ρbar ρA b bbar v (X v)) +
            (-z) • lift ρbar ρA b bbar v (X v)) =
          π₁' ρbar ρA b bbar X (ρA.ρ σ (lift ρbar ρA b bbar v (X v))) +
            π₁' ρbar ρA b bbar X ((-z) • lift ρbar ρA b bbar v (X v)) from by
          simp only [π₁', π₁_add, π₀_add, map_add]; abel] at h1
      rw [π₁'_ρA ρbar ρA b bbar ρd hd hfr c hc, hπ', map_zero, zero_add, π₁'_smul, hπ', smul_zero,
        zero_add, π₀_lift, snd_neg, neg_smul] at h1

      simpa [sub_eq_add_neg] using h1

    set t : k := z.snd / z.fst with ht
    have htx : x.snd / x.fst = t := by
      rw [ht, hxz0, hxz1, mul_div_mul_left _ _ hane]
    have hcw' : c' ρbar c X σ w₀ = t • w₀ := by
      have := congrArg (fun v => x.fst⁻¹ • v) hcw
      simp only [smul_smul, inv_mul_cancel₀ hx0ne, one_smul] at this
      rw [this, ← htx, div_eq_inv_mul]
    have hcu : ∀ u : V̄, c' ρbar c X σ u - t • u ∈ k ∙ w₀ := by
      intro u

      have e : ρbar.ρ σ (ρbar.ρ σ⁻¹ u) = u := by
        rw [← Module.End.mul_apply, ρbar_mul_inv, Module.End.one_apply]
      have h1 := hcz (ρbar.ρ σ⁻¹ u)
      rw [e] at h1

      have h2 := hz0 (ρbar.ρ σ⁻¹ u)
      rw [e] at h2

      have h3 : c' ρbar c X σ u - t • u =
          (c' ρbar c X σ u - z.snd • ρbar.ρ σ⁻¹ u) + (-(z.snd / z.fst)) • (u - z.fst • ρbar.ρ σ⁻¹ u) := by
        rw [ht, neg_smul, smul_sub, smul_smul, div_mul_cancel₀ _ hz0ne]
        abel
      rw [h3]
      exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

    have htr0 : LinearMap.trace k V̄ (c' ρbar c X σ) = 0 := by
      simp only [c', map_add, map_sub]
      rw [LinearMap.trace_mul_comm, ← mul_assoc, ρbar_inv_mul, one_mul, sub_self, add_zero]
      exact trace_cE ρbar c σ
    set f : Module.End k V̄ := c' ρbar c X σ - t • 1 with hfdef
    have hfmem : ∀ u, f u ∈ k ∙ w₀ := fun u => by
      simpa [hfdef] using hcu u
    have hfw : f w₀ = 0 := by
      simp [hfdef, hcw']
    have hf2 : f * f = 0 := by
      ext u
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hfmem u)
      rw [Module.End.mul_apply, ← hr, map_smul, hfw, smul_zero, LinearMap.zero_apply]
    have hftr : LinearMap.trace k V̄ f = 0 := by
      have hnil : IsNilpotent f := ⟨2, by rw [pow_two, hf2]⟩
      exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    have ht0 : t = 0 := by
      have : LinearMap.trace k V̄ (c' ρbar c X σ) = LinearMap.trace k V̄ f + t * 2 := by
        rw [hfdef, map_sub, map_smul, LinearMap.trace_one, ρbar.finrank_eq, smul_eq_mul]
        push_cast
        ring
      rw [htr0, hftr, zero_add] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact h
      · exact absurd h h2
    refine ⟨fun v => ?_, ?_⟩
    · have := hcu v
      rwa [ht0, zero_smul, sub_zero] at this
    · rw [hcw', ht0, zero_smul]

end Strict

section Local

variable (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)

local notation "V̄" => ρbar.V
local notation "Gp" => primeLocalGaloisGroup (pPrime p)
local notation "loc" => primeLocalToGlobal (pPrime p)
local notation "P₀" => primeLocalPlace (pPrime p)
local notation "W" => Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero

lemma loc_mem_decompositionSubgroup (g : Gp) : (loc) g ∈ (P₀).decompositionSubgroup ℚ :=
  localGaloisToGlobal_mem_decompositionSubgroup p g

lemma adZeroFil_le_comap (ℓ : Submodule k V̄) {σ : Γℚ} (hσ : ∀ v ∈ ℓ, ρbar.ρ σ v ∈ ℓ) :
    ρbar.adZeroFil ℓ ≤ (ρbar.adZeroFil ℓ).comap (ρbar.adZeroRep σ) := by
  intro f hf
  obtain ⟨hf1, hf2⟩ := (ρbar.mem_adZeroFil_iff ℓ f).1 hf
  rw [Submodule.mem_comap, ρbar.mem_adZeroFil_iff]
  have hinv : ∀ v ∈ ℓ, ρbar.ρ σ⁻¹ v ∈ ℓ := by

    intro v hv
    set fℓ : ℓ →ₗ[k] ℓ := (ρbar.ρ σ).restrict (p := ℓ) (q := ℓ) (fun x hx => hσ x hx) with hfℓ
    have hsurj : Function.Surjective fℓ := by
      apply LinearMap.surjective_of_injective
      intro a b hab
      exact Subtype.ext (ρbar_injective ρbar σ (congrArg Subtype.val hab))
    obtain ⟨w, hw⟩ := hsurj ⟨v, hv⟩
    have hw' : ρbar.ρ σ w = v := congrArg Subtype.val hw
    have : ρbar.ρ σ⁻¹ v = w := by
      rw [← hw', ← Module.End.mul_apply, ρbar_inv_mul, Module.End.one_apply]
    rw [this]; exact w.2
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [ResidualGaloisRep.adZeroRep_apply_coe, Module.End.mul_apply, Module.End.mul_apply]
    exact hσ _ (hf1 _)
  · rw [ResidualGaloisRep.adZeroRep_apply_coe, Module.End.mul_apply, Module.End.mul_apply,
      hf2 _ (hinv v hv), map_zero]

variable (ℓ : Submodule k ρbar.V)
  (hstab : ∀ σ ∈ (primeLocalPlace (pPrime p)).decompositionSubgroup ℚ, ∀ v ∈ ℓ, ρbar.ρ σ v ∈ ℓ)

def Nρ : Representation k Gp ↥(ρbar.adZeroFil ℓ) :=
  Representation.subrepresentation (ρbar.adZeroRep.comp (loc)) (ρbar.adZeroFil ℓ)
    (fun g => adZeroFil_le_comap ρbar ℓ (hstab _ (loc_mem_decompositionSubgroup p g)))

abbrev Nrep : Rep k Gp := Rep.of (X := ↥(ρbar.adZeroFil ℓ)) (Nρ p ρbar ℓ hstab)

def ιN : Rep.res (MonoidHom.id Gp) (Nrep p ρbar ℓ hstab) ⟶ W :=
  Rep.ofHom
    { toLinearMap := (ρbar.adZeroFil ℓ).subtype
      isIntertwining' := fun g => by ext f; rfl }

def Limg : Submodule k (H1 W) :=
  (continuousH1 (loc) (Nrep p ρbar ℓ hstab)).map (groupCohomology.map (MonoidHom.id Gp) (ιN p ρbar ℓ hstab) 1).hom

variable {p ρbar ℓ hstab}

lemma H1π_mem_Limg (cW : cocycles₁ W) (m : ↥(LinearMap.ker (LinearMap.trace k ρbar.V)))
    (n : Gp → ↥(ρbar.adZeroFil ℓ))
    (hn : ∀ g, (cW g : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) =
      (n g : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) + (ρbar.adZeroRep ((loc) g) m - m))
    (hlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ g s : Gp, (loc) s ∈ F.fixingSubgroup → n (g * s) = n g) :
    H1π W cW ∈ Limg p ρbar ℓ hstab := by

  have hAmul : ∀ g h : Gp, ∀ x : ↥(LinearMap.ker (LinearMap.trace k ρbar.V)),
      ρbar.adZeroRep ((loc) (g * h)) x = ρbar.adZeroRep ((loc) g) (ρbar.adZeroRep ((loc) h) x) := by
    intro g h x
    rw [map_mul, map_mul, Module.End.mul_apply]
  have hn' : ∀ g, ((n g : ↥(ρbar.adZeroFil ℓ)) : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) =
      (cW g : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) - (ρbar.adZeroRep ((loc) g) m - m) := by
    intro g; rw [hn g]; abel
  have hncoc : n ∈ cocycles₁ (Nrep p ρbar ℓ hstab) := by
    rw [mem_cocycles₁_iff]
    intro g h
    have hc := (mem_cocycles₁_iff (A := W) cW).1 cW.2 g h
    apply Subtype.ext
    change ((n (g * h) : ↥(ρbar.adZeroFil ℓ)) : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) =
      ρbar.adZeroRep ((loc) g) (n h : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) +
        (n g : ↥(LinearMap.ker (LinearMap.trace k ρbar.V)))
    have e1 : ((W).ρ g (cW h) : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) =
        ρbar.adZeroRep ((loc) g) (cW h) := rfl
    rw [hn' (g * h), hc, e1, hn' h, hn' g, hAmul, map_sub, map_sub]
    abel
  set nc : cocycles₁ (Nrep p ρbar ℓ hstab) := ⟨n, hncoc⟩ with hncdef
  refine ⟨H1π (Nrep p ρbar ℓ hstab) nc, ?_, ?_⟩
  ·
    obtain ⟨F, hF, hFn⟩ := hlev
    exact H1π_mem_continuousH1 _ _ ⟨F, hF, fun g s hs => hFn g s hs⟩
  ·
    erw [H1π_comp_map_apply]
    rw [H1π_eq_iff]
    refine ⟨-m, funext fun g => ?_⟩
    rw [d₀₁_hom_apply]
    change ρbar.adZeroRep ((loc) g) (-m) - (-m) =
      ((n g : ↥(ρbar.adZeroFil ℓ)) : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) -
        (cW g : ↥(LinearMap.ker (LinearMap.trace k ρbar.V)))
    rw [hn' g, map_neg]
    abel

end Local

section Membership

variable (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k) (ρA : GaloisRepAdic (DualNumber k))
  (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V)
  (ρd : Γℚ →* (DualNumber (Module.End k ρbar.V))ˣ)
  (hd : IsDualLift ρbar.ρ.toHomUnits ρd)
  (hfr : ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩)
  (c : cocycles₁ ρbar.adZero)
  (hc : ∀ σ, ((c : Γℚ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρd σ)

local notation "Gp" => primeLocalGaloisGroup (pPrime p)
local notation "loc" => primeLocalToGlobal (pPrime p)
local notation "P₀" => primeLocalPlace (pPrime p)
local notation "W" => Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero

lemma exists_traceZero_part (h2 : (2 : k) ≠ 0) (X : Module.End k ρbar.V) :
    ∃ X₀ : ↥(LinearMap.ker (LinearMap.trace k ρbar.V)), ∀ σ : Γℚ,
      ρbar.ρ σ * X * ρbar.ρ σ⁻¹ - X =
        ((ρbar.adZeroRep σ X₀ : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) : Module.End k ρbar.V) - X₀ := by
  set t : k := (2 : k)⁻¹ * LinearMap.trace k ρbar.V X with ht
  set X₀ : Module.End k ρbar.V := X - t • (1 : Module.End k ρbar.V) with hX₀
  have htr : LinearMap.trace k ρbar.V X₀ = 0 := by
    rw [hX₀, map_sub, map_smul, LinearMap.trace_one, ρbar.finrank_eq, ht, smul_eq_mul]
    push_cast
    field_simp
    ring
  refine ⟨⟨X₀, LinearMap.mem_ker.2 htr⟩, fun σ => ?_⟩
  rw [ResidualGaloisRep.adZeroRep_apply_coe]
  change _ = ρbar.ρ σ * X₀ * ρbar.ρ σ⁻¹ - X₀
  rw [hX₀]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, ρbar_mul_inv]
  abel

lemma span_stable {D : Subgroup Γℚ} {w₀ : ρbar.V} (h : ∀ σ ∈ D, ρbar.ρ σ w₀ ∈ k ∙ w₀) :
    ∀ σ ∈ D, ∀ v ∈ k ∙ w₀, ρbar.ρ σ v ∈ k ∙ w₀ := by
  intro σ hσ v hv
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [map_smul]
  exact Submodule.smul_mem _ _ (h σ hσ)

include hd hfr hc in

theorem res_mem_Limg [CharP k p] (h2 : (2 : k) ≠ 0) (hstr : ρA.IsStrictOrdinaryAt p) :
    ∃ (w₀ : ρbar.V) (hD : ∀ σ ∈ (P₀).decompositionSubgroup ℚ, ρbar.ρ σ w₀ ∈ k ∙ w₀),
      w₀ ≠ 0 ∧
      (∀ σ ∈ (P₀).inertiaSubgroupIn ℚ, ∀ v : ρbar.V, ρbar.ρ σ v - v ∈ k ∙ w₀) ∧
      (∀ σ ∈ (P₀).decompositionSubgroup ℚ, ∃ x z : k,
        ρbar.ρ σ w₀ = x • w₀ ∧ (∀ v : ρbar.V, ρbar.ρ σ v - z • v ∈ k ∙ w₀) ∧
        ∀ (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
          x - (a : k) * z ∈ Ideal.span {((p ^ n : ℕ) : k)}) ∧
      (groupCohomology.map (loc) (𝟙 W) 1).hom (H1π ρbar.adZero c) ∈
        Limg p ρbar (k ∙ w₀) (span_stable ρbar hD) := by
  obtain ⟨w₀, X, hw₀, hD, hI, hsc, hcoch⟩ :=
    exists_resStrict ρbar ρA b bbar ρd hd hfr c hc p h2 hstr (P₀) (liesOverPrime_primeLocalPlace (pPrime p))
  refine ⟨w₀, hD, hw₀, hI, hsc, ?_⟩
  obtain ⟨X₀, hX₀⟩ := exists_traceZero_part ρbar h2 X

  obtain ⟨-, ⟨F, hF, -, hlevF⟩, -⟩ :=
    GaloisRepAdic.isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt ρbar ρA ρd hd b bbar hfr
  obtain ⟨Lρ, hLρ, hLρ1⟩ := ρbar.factorsThroughFiniteLevel
  haveI := hF; haveI := hLρ

  set cW : cocycles₁ W := (mapCocycles₁ (loc) (𝟙 W)) c with hcW
  have hval : ∀ g, cW g = c ((loc) g) := fun g => rfl
  have hres : (groupCohomology.map (loc) (𝟙 W) 1).hom (H1π ρbar.adZero c) = H1π W cW := by
    erw [H1π_comp_map_apply]
  rw [hres]

  have htr' : ∀ σ, LinearMap.trace k ρbar.V (c' ρbar c X σ) = 0 := by
    intro σ
    simp only [c', map_add, map_sub]
    rw [LinearMap.trace_mul_comm, ← mul_assoc, ρbar_inv_mul, one_mul, sub_self, add_zero]
    exact trace_cE ρbar c σ

  have hmemN : ∀ g : Gp, (⟨c' ρbar c X ((loc) g), LinearMap.mem_ker.2 (htr' _)⟩ :
      ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) ∈ ρbar.adZeroFil (k ∙ w₀) := by
    intro g
    rw [ResidualGaloisRep.mem_adZeroFil_iff]
    obtain ⟨h1, h2'⟩ := hcoch _ (loc_mem_decompositionSubgroup p g)
    refine ⟨fun v => h1 v, fun v hv => ?_⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
    change c' ρbar c X ((loc) g) (t • w₀) = 0
    rw [map_smul, h2', smul_zero]
  refine H1π_mem_Limg cW (-X₀)
    (fun g => ⟨⟨c' ρbar c X ((loc) g), LinearMap.mem_ker.2 (htr' _)⟩, hmemN g⟩) (fun g => ?_) ?_
  ·
    apply Subtype.ext
    rw [hval, Submodule.coe_add, Submodule.coe_sub, map_neg, Submodule.coe_neg]
    change ((c : Γℚ → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) ((loc) g) : Module.End k ρbar.V) =
      c' ρbar c X ((loc) g) +
        (-(((ρbar.adZeroRep ((loc) g) X₀ : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) :
            Module.End k ρbar.V)) - -((X₀ : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) : Module.End k ρbar.V))
    rw [c', cE_def, show -(((ρbar.adZeroRep ((loc) g) X₀ : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) :
            Module.End k ρbar.V)) - -((X₀ : ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) : Module.End k ρbar.V) =
        -(ρbar.ρ ((loc) g) * X * ρbar.ρ ((loc) g)⁻¹ - X) from by rw [hX₀]; abel]
    abel
  ·
    refine ⟨F ⊔ Lρ, IntermediateField.finiteDimensional_sup F Lρ, fun g s hs => ?_⟩
    have hsF : ∀ x ∈ F, (loc) s x = x := fun x hx =>
      (IntermediateField.mem_fixingSubgroup_iff (F ⊔ Lρ) _).1 hs x ((le_sup_left : F ≤ F ⊔ Lρ) hx)
    have hsL : ∀ x ∈ Lρ, (loc) s x = x := fun x hx =>
      (IntermediateField.mem_fixingSubgroup_iff (F ⊔ Lρ) _).1 hs x ((le_sup_right : Lρ ≤ F ⊔ Lρ) hx)
    have hρs : ρbar.ρ ((loc) s) = 1 := hLρ1 _ hsL
    have hρs' : ρbar.ρ ((loc) s)⁻¹ = 1 := by
      have := ρbar_inv_mul ρbar ((loc) s)
      rwa [hρs, mul_one] at this
    apply Subtype.ext; apply Subtype.ext
    change c' ρbar c X ((loc) (g * s)) = c' ρbar c X ((loc) g)
    simp only [c', cE_def, map_mul, hρs, hρs', mul_one, mul_inv_rev, one_mul]
    rw [hc, hc, hlevF _ _ hsF]

end Membership

section ResStrict

variable (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)

local notation "V̄" => ρbar.V
local notation "Gp" => primeLocalGaloisGroup (pPrime p)
local notation "loc" => primeLocalToGlobal (pPrime p)
local notation "P₀" => primeLocalPlace (pPrime p)
local notation "W" => Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero

lemma Limg_congr {ℓ ℓ' : Submodule k ρbar.V} (h : ℓ = ℓ')
    (hs : ∀ σ ∈ (primeLocalPlace (pPrime p)).decompositionSubgroup ℚ, ∀ v ∈ ℓ, ρbar.ρ σ v ∈ ℓ)
    (hs' : ∀ σ ∈ (primeLocalPlace (pPrime p)).decompositionSubgroup ℚ, ∀ v ∈ ℓ', ρbar.ρ σ v ∈ ℓ') :
    Limg p ρbar ℓ hs = Limg p ρbar ℓ' hs' := by
  subst h; rfl

def IsResStrict (w₀ : V̄) : Prop :=
  w₀ ≠ 0 ∧
  (∀ σ ∈ (P₀).decompositionSubgroup ℚ, ρbar.ρ σ w₀ ∈ k ∙ w₀) ∧
  (∀ σ ∈ (P₀).inertiaSubgroupIn ℚ, ∀ v : V̄, ρbar.ρ σ v - v ∈ k ∙ w₀) ∧
  (∀ σ ∈ (P₀).decompositionSubgroup ℚ, ∃ x z : k,
    ρbar.ρ σ w₀ = x • w₀ ∧ (∀ v : V̄, ρbar.ρ σ v - z • v ∈ k ∙ w₀) ∧
    ∀ (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
      x - (a : k) * z ∈ Ideal.span {((p ^ n : ℕ) : k)})

lemma cycloExp_spec (σ : Γℚ) (μ : AlgebraicClosure ℚ) (hμ : μ ^ p = 1) :
    σ μ = μ ^ cycloExp p σ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hμ
    exact zero_ne_one hμ
  have ht : Units.mk0 μ hμ0 ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity']; exact hμ
  have := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) ht
  simpa [cycloExp] using this

variable {p ρbar}

lemma resStrict_scalar_eq [CharP k p] {σ : Γℚ} {x z : k}
    (hxz : ∀ (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
      x - (a : k) * z ∈ Ideal.span {((p ^ n : ℕ) : k)}) :
    x = (cycloExp p σ : k) * z := by
  have h := hxz 1 (cycloExp p σ) (fun μ hμ => cycloExp_spec p σ μ (by rwa [pow_one] at hμ))
  rwa [pow_one, CharP.cast_eq_zero, Ideal.span_singleton_zero, Ideal.mem_bot, sub_eq_zero] at h

theorem span_eq_of_isResStrict [CharP k p] (hp2 : p ≠ 2) {w₀ w₀' : V̄}
    (h : IsResStrict p ρbar w₀) (h' : IsResStrict p ρbar w₀') : (k ∙ w₀) = (k ∙ w₀') := by
  obtain ⟨hw₀, hD, hI, hsc⟩ := h
  obtain ⟨hw₀', hD', hI', hsc'⟩ := h'
  by_contra hne

  have hnot : w₀' ∉ k ∙ w₀ := by
    intro hmem
    apply hne
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hmem
    have ht : t ≠ 0 := by rintro rfl; exact hw₀' (zero_smul _ _)
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem]
      have : t⁻¹ • (t • w₀) ∈ k ∙ (t • w₀) :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

  have hmeet : ∀ v, v ∈ k ∙ w₀ → v ∈ k ∙ w₀' → v = 0 := by
    intro v hv hv'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv'
    by_cases ha : a = 0
    · rw [ha, zero_smul]
    · exfalso
      apply hnot
      have : w₀' = a⁻¹ • (a • w₀') := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hv

  obtain ⟨σ, hσI, hnσ⟩ := FreyPackage.exists_inertia_cycloPinned_ne_one_v2 p Fact.out hp2 (P₀)
    (liesOverPrime_primeLocalPlace (pPrime p)) (cycloExp p) (fun σ ζ hζ => cycloExp_spec p σ ζ hζ)
  have hσIn : (σ : Γℚ) ∈ (P₀).inertiaSubgroupIn ℚ := ⟨σ, hσI, rfl⟩
  have hσD : (σ : Γℚ) ∈ (P₀).decompositionSubgroup ℚ := σ.2

  have htriv : ∀ v : V̄, ρbar.ρ (σ : Γℚ) v = v := fun v =>
    sub_eq_zero.1 (hmeet _ (hI _ hσIn v) (hI' _ hσIn v))
  obtain ⟨x, z, hx, hz, hxz⟩ := hsc _ hσD
  have hx1 : x = 1 := by
    rw [htriv] at hx
    have : (x - 1) • w₀ = 0 := by rw [sub_smul, one_smul, ← hx, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact (sub_eq_zero.1 h)
    · exact absurd h hw₀
  have hz1 : z = 1 := by
    have h1 := hz w₀'
    rw [htriv] at h1
    have h2 : w₀' - z • w₀' ∈ k ∙ w₀' :=
      Submodule.sub_mem _ (Submodule.mem_span_singleton_self _)
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    have h3 := hmeet _ h1 h2
    have : (1 - z) • w₀' = 0 := by rwa [sub_smul, one_smul]
    rcases smul_eq_zero.1 this with h | h
    · exact (sub_eq_zero.1 h).symm
    · exact absurd h hw₀'
  have hxω := resStrict_scalar_eq hxz
  rw [hx1, hz1, mul_one] at hxω
  apply hnσ

  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) k) := (ZMod.castHom (dvd_refl p) k).injective
  apply hinj
  rw [map_natCast, map_one]
  exact hxω.symm

end ResStrict

section Count

variable (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)

local notation "V̄" => ρbar.V
local notation "Gp" => primeLocalGaloisGroup (pPrime p)
local notation "loc" => primeLocalToGlobal (pPrime p)
local notation "P₀" => primeLocalPlace (pPrime p)
local notation "W" => Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero
local notation "E" => (LinearMap.ker (LinearMap.trace k ρbar.V))

variable {p ρbar}
variable {w₀ : ρbar.V} (hrs : IsResStrict p ρbar w₀)

lemma sub_smul_sub {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (S : Submodule R M)
    (a b : R) (x : ↥S) : a • x - b • x = (a - b) • x := (sub_smul a b x).symm

lemma forall_mem_of_basis (bV : Module.Basis (Fin 2) k V̄) (ℓ : Submodule k V̄) (f : Module.End k V̄)
    (h0 : f (bV 0) ∈ ℓ) (h1 : f (bV 1) ∈ ℓ) : ∀ v, f v ∈ ℓ := by
  intro v
  rw [← bV.sum_repr v, map_sum, Fin.sum_univ_two, map_smul, map_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1)

lemma endo_ext (bV : Module.Basis (Fin 2) k V̄) {f g : Module.End k V̄}
    (h0 : f (bV 0) = g (bV 0)) (h1 : f (bV 1) = g (bV 1)) : f = g :=
  bV.ext fun i => by fin_cases i <;> assumption

include hrs in

lemma adZeroRep_apply_eq_smul [CharP k p] {σ : Γℚ} (hσ : σ ∈ (P₀).decompositionSubgroup ℚ)
    (f : E) (hf : f ∈ ρbar.adZeroFil (k ∙ w₀)) :
    ρbar.adZeroRep σ f = (cycloExp p σ : k) • f := by
  obtain ⟨hw₀, hD, hI, hsc⟩ := hrs
  obtain ⟨x, z, hx, hz, hxz⟩ := hsc σ hσ
  have hxω := resStrict_scalar_eq hxz
  obtain ⟨hf1, hf2⟩ := (ρbar.mem_adZeroFil_iff _ f).1 hf
  apply Subtype.ext
  rw [ResidualGaloisRep.adZeroRep_apply_coe, Submodule.coe_smul]

  have key : ∀ v, ρbar.ρ σ ((f : Module.End k V̄) v) = (cycloExp p σ : k) • (f : Module.End k V̄) (ρbar.ρ σ v) := by
    intro v
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hf1 v)
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 (hz v)
    have e1 : ρbar.ρ σ v = s • w₀ + z • v := by rw [hs]; abel
    rw [← hr, map_smul, hx, e1, map_add, map_smul, map_smul,
      hf2 _ (Submodule.mem_span_singleton_self _), smul_zero, zero_add, ← hr, hxω, smul_smul,
      smul_smul, smul_smul]
    congr 1; ring
  ext v
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply, key,
    ← Module.End.mul_apply (ρbar.ρ σ), ρbar_mul_inv, Module.End.one_apply]

variable (p ρbar w₀) in

lemma hstab_of (hD : ∀ σ ∈ (P₀).decompositionSubgroup ℚ, ρbar.ρ σ w₀ ∈ k ∙ w₀) :
    ∀ σ ∈ (P₀).decompositionSubgroup ℚ, ∀ v ∈ k ∙ w₀, ρbar.ρ σ v ∈ k ∙ w₀ :=
  span_stable ρbar hD

include hrs in

lemma Nρ_apply [CharP k p] (g : Gp) (n : ↥(ρbar.adZeroFil (k ∙ w₀))) :
    Nρ p ρbar (k ∙ w₀) (hstab_of p ρbar w₀ hrs.2.1) g n = (cycloExp p ((loc) g) : k) • n := by
  apply Subtype.ext
  change ρbar.adZeroRep ((loc) g) n = _
  rw [adZeroRep_apply_eq_smul hrs (loc_mem_decompositionSubgroup p g) n n.2, Submodule.coe_smul]

lemma cast_cycloChar_loc (g : Gp) [CharP k p] :
    (cycloExp p ((loc) g) : k) =
      ZMod.castHom (dvd_refl p) k (((cycloChar p).comp (loc) g : (ZMod p)ˣ) : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [MonoidHom.comp_apply, ZMod.castHom_apply, ← val_cycloChar, ZMod.natCast_val]

include hrs in

theorem finrank_continuousH1_N_le [Finite k] [CharP k p] (hp2 : p ≠ 2) :
    ∃ S : Submodule k (H1 (Nrep p ρbar (k ∙ w₀) (hstab_of p ρbar w₀ hrs.2.1))),
      FiniteDimensional k S ∧ finrank k S ≤ 2 ∧
      continuousH1 (loc) (Nrep p ρbar (k ∙ w₀) (hstab_of p ρbar w₀ hrs.2.1)) ≤ S := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set hst := hstab_of p ρbar w₀ hrs.2.1
  set N := Nrep p ρbar (k ∙ w₀) hst with hNdef
  obtain ⟨hw₀, hD, hI, hsc⟩ := hrs

  set χ : Gp →* (ZMod p)ˣ := (cycloChar p).comp (loc) with hχ
  set M : Rep (ZMod p) Gp := ofChar (k := ZMod p) χ with hM
  have hMρ : ∀ (g : Gp) (r : ZMod p), M.ρ g r = (χ g : ZMod p) * r := fun g r => rfl
  obtain ⟨hMfin, hM2⟩ := groupCohomology.finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal
    hp2 (pPrime p) rfl (continuousH1 (loc) M) (fun x => by rw [mem_continuousH1_iff]; rfl)
  haveI := hMfin
  set bC := Module.finBasisOfFinrankEq (ZMod p) (continuousH1 (loc) M) hM2 with hbC
  have hrep : ∀ j : Fin 2, ∃ c : cocycles₁ M, IsLevelConstant₁ (loc) c ∧ (H1π M).hom c = bC j :=
    fun j => (mem_continuousH1_iff (loc) M _).1 (bC j).2
  choose cM hcMlev hcMπ using hrep

  set ι : ZMod p →+* k := ZMod.castHom (dvd_refl p) k with hι
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  have hsmul : ∀ (r : ZMod p) (x : k), r • x = ι r * x := fun r x => rfl
  haveI : Module.Finite (ZMod p) k := Module.Finite.of_finite
  set bk := Module.finBasis (ZMod p) k with hbk

  have hlt : (k ∙ w₀) < ⊤ := by
    apply lt_top_iff_ne_top.2
    intro htop
    have := finrank_span_singleton (K := k) hw₀
    rw [htop, finrank_top, ρbar.finrank_eq] at this
    exact absurd this (by norm_num)
  obtain ⟨u, -, hu⟩ := SetLike.exists_of_lt hlt
  have hli : LinearIndependent k ![u, w₀] := by
    rw [linearIndependent_fin2]
    refine ⟨hw₀, fun a ha => hu ?_⟩
    exact Submodule.mem_span_singleton.2 ⟨a, ha⟩
  set bV : Module.Basis (Fin 2) k V̄ := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, ρbar.finrank_eq]) with hbVdef
  have hbV0 : bV 0 = u := by rw [hbVdef, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hbV1 : bV 1 = w₀ := by rw [hbVdef, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  set n₀E : Module.End k V̄ := bV.constr k ![w₀, (0 : V̄)] with hn₀E
  have hn₀u : n₀E u = w₀ := by
    have := bV.constr_basis k ![w₀, (0 : V̄)] 0
    rwa [hbV0] at this
  have hn₀w : n₀E w₀ = 0 := by
    have := bV.constr_basis k ![w₀, (0 : V̄)] 1
    rwa [hbV1] at this
  have hn₀mem : ∀ v, n₀E v ∈ k ∙ w₀ := by
    refine forall_mem_of_basis bV _ _ ?_ ?_
    · rw [hbV0, hn₀u]; exact Submodule.mem_span_singleton_self _
    · rw [hbV1, hn₀w]; exact Submodule.zero_mem _
  have hn₀kill : ∀ v ∈ k ∙ w₀, n₀E v = 0 := by
    intro v hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul, hn₀w, smul_zero]
  have hn₀sq : n₀E * n₀E = 0 := by
    ext v; rw [Module.End.mul_apply, hn₀kill _ (hn₀mem v), LinearMap.zero_apply]
  have hn₀tr : LinearMap.trace k V̄ n₀E = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent ⟨2, by rw [pow_two, hn₀sq]⟩).eq_zero
  set n₀ : ↥(ρbar.adZeroFil (k ∙ w₀)) :=
    ⟨⟨n₀E, LinearMap.mem_ker.2 hn₀tr⟩, (ρbar.mem_adZeroFil_iff _ _).2 ⟨hn₀mem, hn₀kill⟩⟩ with hn₀

  set coord : ↥(ρbar.adZeroFil (k ∙ w₀)) →ₗ[k] k :=
    (bV.coord 1) ∘ₗ (LinearMap.applyₗ u) ∘ₗ (LinearMap.ker (LinearMap.trace k ρbar.V)).subtype ∘ₗ
      (ρbar.adZeroFil (k ∙ w₀)).subtype with hcoord
  have hcoord_apply : ∀ f : ↥(ρbar.adZeroFil (k ∙ w₀)),
      coord f = bV.repr (((f : E) : Module.End k V̄) u) 1 := fun f => rfl
  have hcoord_eq : ∀ f : ↥(ρbar.adZeroFil (k ∙ w₀)), f = coord f • n₀ := by
    intro f
    obtain ⟨hf1, hf2⟩ := (ρbar.mem_adZeroFil_iff _ _).1 f.2
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hf1 u)
    have hcr : coord f = r := by
      rw [hcoord_apply, ← hr, map_smul, Finsupp.smul_apply, ← hbV1, bV.repr_self,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    apply Subtype.ext; apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_smul, hcr]
    change ((f : E) : Module.End k V̄) = r • n₀E
    refine endo_ext bV ?_ ?_
    · rw [hbV0, LinearMap.smul_apply, hn₀u, hr]
    · rw [hbV1, LinearMap.smul_apply, hn₀w, smul_zero]
      exact hf2 _ (Submodule.mem_span_singleton_self _)

  have hNρ : ∀ (g : Gp) (n : ↥(ρbar.adZeroFil (k ∙ w₀))), N.ρ g n = ι (χ g : ZMod p) • n := by
    intro g n
    have := Nρ_apply (p := p) (ρbar := ρbar) ⟨hw₀, hD, hI, hsc⟩ g n
    rw [cast_cycloChar_loc] at this
    exact this
  clear_value coord n₀ ι
  clear_value n₀E bV

  have hĉmem : ∀ j : Fin 2, (fun g : Gp => ι (cM j g) • n₀) ∈ cocycles₁ N := by
    intro j
    rw [mem_cocycles₁_iff]
    intro g h
    have hc := (mem_cocycles₁_iff (A := M) (cM j)).1 (cM j).2 g h
    rw [hMρ] at hc
    show ι (cM j (g * h)) • n₀ = N.ρ g (ι (cM j h) • n₀) + ι (cM j g) • n₀
    rw [hc, map_add, map_mul, add_smul, mul_smul, map_smul, hNρ, smul_smul, smul_smul, mul_comm]
  set ĉ : Fin 2 → cocycles₁ N := fun j => ⟨_, hĉmem j⟩ with hĉ

  refine ⟨Submodule.span k (Set.range fun j => (H1π N).hom (ĉ j)),
    FiniteDimensional.span_of_finite k (Set.finite_range _),
    (finrank_range_le_card _).trans (by rw [Fintype.card_fin]), ?_⟩
  intro y hy
  obtain ⟨c, hclev, rfl⟩ := (mem_continuousH1_iff (loc) N y).1 hy

  set γ : Gp → k := fun g => coord (c g) with hγ
  have hcγ : ∀ g, c g = γ g • n₀ := fun g => hcoord_eq (c g)
  have hγcoc : ∀ g h, γ (g * h) = ι (χ g : ZMod p) * γ h + γ g := by
    intro g h
    have hc := (mem_cocycles₁_iff (A := N) c).1 c.2 g h
    have := congrArg coord hc
    rw [map_add, hNρ, map_smul, smul_eq_mul] at this
    exact this
  have hγlev : IsLevelConstant₁ (loc) γ := hclev.comp coord
  clear_value γ

  set γc : Fin (finrank (ZMod p) k) → Gp → ZMod p := fun i g => bk.repr (γ g) i with hγc
  have hγcmem : ∀ i, γc i ∈ cocycles₁ M := by
    intro i
    rw [mem_cocycles₁_iff]
    intro g h
    simp only [hγc]
    rw [hγcoc, hMρ, ← hsmul, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hγclev : ∀ i, IsLevelConstant₁ (loc) (γc i) := fun i => hγlev.comp (fun x => bk.repr x i)

  have hdec : ∀ i, ∃ (r : Fin 2 → ZMod p) (m : ZMod p),
      ∀ g, γc i g = ∑ j, r j * cM j g + ((χ g : ZMod p) * m - m) := by
    intro i
    have hmem : (H1π M).hom ⟨γc i, hγcmem i⟩ ∈ continuousH1 (loc) M :=
      H1π_mem_continuousH1 _ _ (hγclev i)
    set yi : ↥(continuousH1 (loc) M) := ⟨_, hmem⟩ with hyi
    have hsum : ((H1π M).hom ⟨γc i, hγcmem i⟩ : H1 M) = ∑ j, bC.repr yi j • (bC j : H1 M) := by
      conv_lhs => rw [show (H1π M).hom ⟨γc i, hγcmem i⟩ = (yi : H1 M) from rfl, ← bC.sum_repr yi]
      rw [Submodule.coe_sum]
      rfl
    have hsum' : (H1π M).hom ⟨γc i, hγcmem i⟩ = (H1π M).hom (∑ j, bC.repr yi j • cM j) := by
      rw [hsum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hcMπ]
    have hcob := (H1π_eq_iff (A := M) _ _).1 hsum'
    obtain ⟨m, hm⟩ := hcob
    refine ⟨fun j => bC.repr yi j, m, fun g => ?_⟩
    have hmg := congrFun hm g
    rw [d₀₁_hom_apply, hMρ] at hmg
    change (χ g : ZMod p) * m - m =
      γc i g - ((∑ j, bC.repr yi j • cM j : cocycles₁ M) : Gp → ZMod p) g at hmg
    have hsumg : ((∑ j, bC.repr yi j • cM j : cocycles₁ M) : Gp → ZMod p) g =
        ∑ j, bC.repr yi j * cM j g := by
      rw [← cocycles₁.val_eq_coe, Submodule.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, cocycles₁.val_eq_coe]
    rw [hsumg] at hmg
    rw [hmg]; ring
  choose r m hrm using hdec

  set α : Fin 2 → k := fun j => ∑ i, r i j • bk i with hα
  set mk : k := ∑ i, m i • bk i with hmk
  have hγeq : ∀ g, γ g = ∑ j, ι (cM j g) * α j + (ι (χ g : ZMod p) * mk - mk) := by
    intro g
    conv_lhs => rw [← bk.sum_repr (γ g)]
    simp only [hα, hmk, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change γc i g • bk i = _
    rw [hrm i g, add_smul, Finset.sum_smul, sub_smul]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hsmul, map_mul]
      ring
    · simp only [hsmul, map_mul]
      ring
  clear_value α mk

  have hclass : (H1π N).hom c = ∑ j, α j • (H1π N).hom (ĉ j) := by
    have : ∑ j, α j • (H1π N).hom (ĉ j) = (H1π N).hom (∑ j, α j • ĉ j) := by
      rw [map_sum]; simp only [map_smul]
    rw [this, H1π_eq_iff]
    refine ⟨mk • n₀, funext fun g => ?_⟩
    rw [d₀₁_hom_apply, hNρ]
    change ι (χ g : ZMod p) • mk • n₀ - mk • n₀ =
      (c g : ↥(ρbar.adZeroFil (k ∙ w₀))) -
        ((∑ j, α j • ĉ j : cocycles₁ N) : Gp → ↥(ρbar.adZeroFil (k ∙ w₀))) g
    have hs : ((∑ j, α j • ĉ j : cocycles₁ N) : Gp → ↥(ρbar.adZeroFil (k ∙ w₀))) g =
        (∑ j, α j * ι (cM j g)) • n₀ := by
      rw [← cocycles₁.val_eq_coe, Submodule.coe_sum, Finset.sum_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, Pi.smul_apply, mul_smul]
    have e3 : ι (χ g : ZMod p) * mk - mk = γ g - ∑ j, α j * ι (cM j g) := by
      rw [hγeq g, Finset.sum_congr rfl fun j _ => mul_comm (ι (cM j g)) (α j), add_sub_cancel_left]
    rw [hs, hcγ g, ← mul_smul, sub_smul_sub, sub_smul_sub, e3]
  rw [hclass]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma exists_basis_of_ne_zero (hw₀ : w₀ ≠ 0) : ∃ bV : Module.Basis (Fin 2) k V̄, bV 1 = w₀ := by
  have hlt : (k ∙ w₀) < ⊤ := by
    apply lt_top_iff_ne_top.2
    intro htop
    have := finrank_span_singleton (K := k) hw₀
    rw [htop, finrank_top, ρbar.finrank_eq] at this
    exact absurd this (by norm_num)
  obtain ⟨u, -, hu⟩ := SetLike.exists_of_lt hlt
  have hli : LinearIndependent k ![u, w₀] := by
    rw [linearIndependent_fin2]
    refine ⟨hw₀, fun a ha => hu ?_⟩
    exact Submodule.mem_span_singleton.2 ⟨a, ha⟩
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, ρbar.finrank_eq]),
    by rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rfl⟩

include hrs in

theorem exists_ne_zero_mem_ker [CharP k p]
    (hinv : (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants = ⊥) :
    ∃ y : H1 (Nrep p ρbar (k ∙ w₀) (hstab_of p ρbar w₀ hrs.2.1)),
      y ≠ 0 ∧ y ∈ continuousH1 (loc) (Nrep p ρbar (k ∙ w₀) (hstab_of p ρbar w₀ hrs.2.1)) ∧
      (groupCohomology.map (MonoidHom.id Gp) (ιN p ρbar (k ∙ w₀) (hstab_of p ρbar w₀ hrs.2.1)) 1).hom y
        = 0 := by
  set hst := hstab_of p ρbar w₀ hrs.2.1
  set N := Nrep p ρbar (k ∙ w₀) hst with hNdef
  obtain ⟨hw₀, hD, hI, hsc⟩ := hrs
  obtain ⟨bV, hbV1⟩ := exists_basis_of_ne_zero (ρbar := ρbar) hw₀
  set u := bV 0 with hu

  set n₀E : Module.End k V̄ := bV.constr k ![w₀, (0 : V̄)] with hn₀E
  set m₀E : Module.End k V̄ := bV.constr k ![(0 : V̄), u] with hm₀E
  have hn₀u : n₀E u = w₀ := by rw [hu]; exact (bV.constr_basis k ![w₀, (0 : V̄)] 0).trans rfl
  have hn₀w : n₀E w₀ = 0 := by rw [← hbV1]; exact (bV.constr_basis k ![w₀, (0 : V̄)] 1).trans rfl
  have hm₀u : m₀E u = 0 := by rw [hu]; exact (bV.constr_basis k ![(0 : V̄), u] 0).trans rfl
  have hm₀w : m₀E w₀ = u := by rw [← hbV1]; exact (bV.constr_basis k ![(0 : V̄), u] 1).trans rfl
  set h : Module.End k V̄ := n₀E * m₀E - m₀E * n₀E with hh
  have hhu : h u = -u := by
    simp only [hh, LinearMap.sub_apply, Module.End.mul_apply, hm₀u, map_zero, hn₀u, hm₀w, zero_sub]
  have hhw : h w₀ = w₀ := by
    simp only [hh, LinearMap.sub_apply, Module.End.mul_apply, hm₀w, hn₀u, hn₀w, map_zero, sub_zero]
  have hhtr : LinearMap.trace k V̄ h = 0 := by
    rw [hh, map_sub, LinearMap.trace_mul_comm, sub_self]
  clear_value n₀E m₀E
  set hZ : E := ⟨h, LinearMap.mem_ker.2 hhtr⟩ with hhZ

  have hmemN : ∀ σ ∈ (P₀).decompositionSubgroup ℚ,
      ρbar.adZeroRep σ hZ - hZ ∈ ρbar.adZeroFil (k ∙ w₀) := by
    intro σ hσ
    obtain ⟨x, z, hx, hz, -⟩ := hsc σ hσ
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 (hz u)
    have eu : ρbar.ρ σ u = s • w₀ + z • u := by rw [hs]; abel

    set g' : Module.End k V̄ := ρbar.ρ σ * h - h * ρbar.ρ σ with hg'
    have hg'w : g' w₀ = 0 := by
      simp only [hg', LinearMap.sub_apply, Module.End.mul_apply, hhw, hx, map_smul, sub_self]
    have hg'u : g' u ∈ k ∙ w₀ := by
      have : g' u = (-(2 : k) * s) • w₀ := by
        simp only [hg', LinearMap.sub_apply, Module.End.mul_apply, hhu, map_neg, eu, map_add, map_smul,
          hhw, smul_neg]
        rw [neg_mul, neg_smul, mul_smul, two_smul]
        abel
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hg'mem : ∀ v, g' v ∈ k ∙ w₀ := by
      refine forall_mem_of_basis bV _ _ (by rw [← hu]; exact hg'u) (by rw [hbV1, hg'w]; exact zero_mem _)
    have hg'kill : ∀ v ∈ k ∙ w₀, g' v = 0 := by
      intro v hv
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hg'w, smul_zero]

    have hAd : ∀ v, ((ρbar.adZeroRep σ hZ - hZ : E) : Module.End k V̄) v = g' (ρbar.ρ σ⁻¹ v) := by
      intro v
      rw [Submodule.coe_sub, ResidualGaloisRep.adZeroRep_apply_coe, LinearMap.sub_apply]
      change (ρbar.ρ σ * h * ρbar.ρ σ⁻¹) v - h v = g' (ρbar.ρ σ⁻¹ v)
      simp only [hg', LinearMap.sub_apply, Module.End.mul_apply]
      rw [← Module.End.mul_apply (ρbar.ρ σ) (ρbar.ρ σ⁻¹), ρbar_mul_inv, Module.End.one_apply]
    have hinvD : σ⁻¹ ∈ (P₀).decompositionSubgroup ℚ := Subgroup.inv_mem _ hσ
    rw [ResidualGaloisRep.mem_adZeroFil_iff]
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [hAd]; exact hg'mem _
    · rw [hAd]; exact hg'kill _ (span_stable ρbar hD _ hinvD v hv)

  set δf : Gp → ↥(ρbar.adZeroFil (k ∙ w₀)) :=
    fun g => ⟨ρbar.adZeroRep ((loc) g) hZ - hZ, hmemN _ (loc_mem_decompositionSubgroup p g)⟩ with hδf
  have hδval : ∀ g, ((δf g : ↥(ρbar.adZeroFil (k ∙ w₀))) : E) = ρbar.adZeroRep ((loc) g) hZ - hZ :=
    fun g => rfl
  have hδmem : δf ∈ cocycles₁ N := by
    rw [mem_cocycles₁_iff]
    intro g g'
    apply Subtype.ext
    rw [Submodule.coe_add, hδval, hδval]
    change _ = ρbar.adZeroRep ((loc) g) (δf g') + _
    rw [hδval, map_mul, map_mul, Module.End.mul_apply, map_sub]
    abel
  set δc : cocycles₁ N := ⟨δf, hδmem⟩ with hδc
  refine ⟨(H1π N).hom δc, ?_, ?_, ?_⟩
  ·
    intro h0
    have h0' : H1π N δc = 0 := h0
    rw [H1π_eq_zero_iff] at h0'
    obtain ⟨n, hn⟩ := h0'
    have hfix : (hZ - (n : E)) ∈ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants := by
      rw [Representation.mem_invariants]
      intro g
      have hg := congrFun hn g
      rw [d₀₁_hom_apply] at hg
      have hg' := congrArg (Subtype.val) hg
      rw [Submodule.coe_sub] at hg'
      change ρbar.adZeroRep ((loc) g) n - n = ρbar.adZeroRep ((loc) g) hZ - hZ at hg'
      change ρbar.adZeroRep ((loc) g) (hZ - n) = hZ - n
      rw [map_sub]
      exact (sub_eq_sub_iff_sub_eq_sub.1 hg'.symm)
    rw [hinv, Submodule.mem_bot, sub_eq_zero] at hfix
    have hmem : (hZ : E) ∈ ρbar.adZeroFil (k ∙ w₀) := by rw [hfix]; exact n.2
    have := ((ρbar.mem_adZeroFil_iff _ _).1 hmem).2 w₀ (Submodule.mem_span_singleton_self _)
    change h w₀ = 0 at this
    rw [hhw] at this
    exact hw₀ this
  ·
    obtain ⟨Lρ, hLρ, hLρ1⟩ := ρbar.factorsThroughFiniteLevel
    refine H1π_mem_continuousH1 _ _ ⟨Lρ, hLρ, fun g s hs => ?_⟩
    have hρs : ρbar.ρ ((loc) s) = 1 :=
      hLρ1 _ (fun x hx => (IntermediateField.mem_fixingSubgroup_iff Lρ _).1 hs x hx)
    have hρs' : ρbar.ρ ((loc) s)⁻¹ = 1 := by
      have := ρbar_inv_mul ρbar ((loc) s)
      rwa [hρs, mul_one] at this
    apply Subtype.ext; apply Subtype.ext
    change ((ρbar.adZeroRep ((loc) (g * s)) hZ - hZ : E) : Module.End k V̄) =
      ((ρbar.adZeroRep ((loc) g) hZ - hZ : E) : Module.End k V̄)
    rw [Submodule.coe_sub, Submodule.coe_sub, ResidualGaloisRep.adZeroRep_apply_coe,
      ResidualGaloisRep.adZeroRep_apply_coe, map_mul, map_mul, mul_inv_rev, map_mul, hρs, hρs',
      mul_one, one_mul]
  ·
    have : (groupCohomology.map (MonoidHom.id Gp) (ιN p ρbar (k ∙ w₀) hst) 1).hom ((H1π N).hom δc) =
        (groupCohomology.map (MonoidHom.id Gp) (ιN p ρbar (k ∙ w₀) hst) 1) (H1π N δc) := rfl
    rw [this, H1π_comp_map_apply, H1π_eq_zero_iff]
    exact ⟨hZ, funext fun g => by rw [d₀₁_hom_apply]; rfl⟩

include hrs in

theorem finrank_Limg_le [Finite k] [CharP k p] (hp2 : p ≠ 2) :
    FiniteDimensional k (Limg p ρbar (k ∙ w₀) (hstab_of p ρbar w₀ hrs.2.1)) ∧
    finrank k (Limg p ρbar (k ∙ w₀) (hstab_of p ρbar w₀ hrs.2.1)) ≤
      finrank k (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants + 1 := by
  set hst := hstab_of p ρbar w₀ hrs.2.1
  set N := Nrep p ρbar (k ∙ w₀) hst with hNdef
  obtain ⟨S, hSfd, hS2, hCS⟩ := finrank_continuousH1_N_le hrs hp2
  haveI := hSfd
  set C := continuousH1 (loc) N with hC
  haveI hCfd : FiniteDimensional k C := Submodule.finiteDimensional_of_le hCS
  have hC2 : finrank k C ≤ 2 := (Submodule.finrank_mono hCS).trans hS2
  set π := (groupCohomology.map (MonoidHom.id Gp) (ιN p ρbar (k ∙ w₀) hst) 1).hom with hπ
  have hL : Limg p ρbar (k ∙ w₀) hst = C.map π := rfl
  rw [hL]
  refine ⟨inferInstance, ?_⟩
  by_cases hinv : (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants = ⊥
  ·
    obtain ⟨y, hy0, hyC, hyπ⟩ := exists_ne_zero_mem_ker hrs hinv
    rw [hinv, finrank_bot, zero_add]
    set f : C →ₗ[k] H1 W := π ∘ₗ C.subtype with hf
    have hrange : LinearMap.range f = C.map π := by rw [hf, LinearMap.range_comp, Submodule.range_subtype]
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange] at hrn
    have hker : 1 ≤ finrank k (LinearMap.ker f) := by
      rw [Submodule.one_le_finrank_iff]
      intro hbot
      have : (⟨y, hyC⟩ : C) ∈ LinearMap.ker f := by
        rw [LinearMap.mem_ker, hf, LinearMap.comp_apply, Submodule.subtype_apply]; exact hyπ
      rw [hbot, Submodule.mem_bot] at this
      exact hy0 (congrArg Subtype.val this)
    omega
  · have h1 : 1 ≤ finrank k (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants := by
      haveI : FiniteDimensional k (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants :=
        FiniteDimensional.finiteDimensional_submodule _
      rw [Submodule.one_le_finrank_iff]; exact hinv
    calc finrank k (C.map π) ≤ finrank k C := Submodule.finrank_map_le _ _
      _ ≤ 2 := hC2
      _ ≤ _ := by omega

end Count

end P2mBpStr

end

open P2mBpStr in
theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k) :
    ∃ L : Submodule k (H1 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)),
      FiniteDimensional k L ∧
      Module.finrank k L ≤
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants + 1 ∧
      ∀ (ρA : GaloisRepAdic (DualNumber k)), ρA.IsStrictOrdinaryAt p →
        ∀ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ,
          IsDualLift ρbar.ρ.toHomUnits ρd →
          (∃ (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V),
            ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
              Matrix.dualNumberEquiv.symm
                ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
                  LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩) →
          ∀ c : cocycles₁ ρbar.adZero,
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) →
            (groupCohomology.map (primeLocalToGlobal (pPrime p))
              (𝟙 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) 1).hom (H1π ρbar.adZero c) ∈ L := by
  classical
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  by_cases hex : ∃ w₀ : ρbar.V, IsResStrict p ρbar w₀
  · obtain ⟨w₀, hrs⟩ := hex
    obtain ⟨hfd, hle⟩ := finrank_Limg_le hrs hp2
    refine ⟨Limg p ρbar (k ∙ w₀) (hstab_of p ρbar w₀ hrs.2.1), hfd, hle, ?_⟩
    intro ρA hstr ρd hd hfr c hc
    obtain ⟨b, bbar, hfr⟩ := hfr
    obtain ⟨w₀', hD', hw₀', hI', hsc', hmem⟩ := res_mem_Limg p ρbar ρA b bbar ρd hd hfr c hc h2 hstr
    have hrs' : IsResStrict p ρbar w₀' := ⟨hw₀', hD', hI', hsc'⟩
    have heq : (k ∙ w₀') = (k ∙ w₀) := span_eq_of_isResStrict hp2 hrs' hrs
    rw [Limg_congr p ρbar heq (span_stable ρbar hD') (hstab_of p ρbar w₀ hrs.2.1)] at hmem
    exact hmem
  · refine ⟨⊥, inferInstance, by simp, ?_⟩
    intro ρA hstr ρd hd hfr c hc
    obtain ⟨b, bbar, hfr⟩ := hfr
    obtain ⟨w₀', hD', hw₀', hI', hsc', -⟩ := res_mem_Limg p ρbar ρA b bbar ρd hd hfr c hc h2 hstr
    exact absurd ⟨w₀', hw₀', hD', hI', hsc'⟩ hex

end S_GaloisRepAdic_exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt
end P2MW
export P2MW.S_GaloisRepAdic_exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt (solution)
