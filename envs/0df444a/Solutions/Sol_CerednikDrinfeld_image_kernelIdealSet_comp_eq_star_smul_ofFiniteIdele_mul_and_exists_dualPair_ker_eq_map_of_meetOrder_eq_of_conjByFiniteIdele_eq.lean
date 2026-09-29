-- Prove2me | solution 1 for CerednikDrinfeld.image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_and_exists_dualPair_ker_eq_map_of_meetOrder_eq_of_conjByFiniteIdele_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0bce8bf4-cba4-5724-8bc8-212ec87a45f6

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_neg_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
import Theorems.Thm_CerednikDrinfeld_image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime
import Theorems.Thm_QuaternionAlgebra_inv_mul_mem_finiteAdeleBox_and_smul_mul_mem_of_mem_primeHeckeSet_of_conjByFiniteIdele_meetOrder_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_and_exists_dualPair_ker_eq_map_of_meetOrder_eq_of_conjByFiniteIdele_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange CerednikDrinfeld ModularCurve AlgebraicCurve"

namespace ALDict

variable {a b : ℚ}

local notation "𝔸H" => ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ

section Adelic

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x y : 𝔸H}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add u w _ _ hu hw => rw [add_mul]; exact add_mem hu hw
    | neg u _ hu =>
      convert neg_mem hu using 1
      exact neg_mul u _
  | zero => rw [mul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mul_add]; exact add_mem hu hw
  | neg u _ hu =>
    convert neg_mem hu using 1
    exact mul_neg x u

theorem intCast_smul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : 𝔸H}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (k : ℤ) : (k : ℚ) • x ∈ Submodule.finiteAdeleBox Λ := by
  rw [Int.cast_smul_eq_zsmul]
  exact AddSubgroup.zsmul_mem _ hx k

theorem ofFiniteIdele_le_of_inv_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (g g' : (𝔸H)ˣ)
    (h : ((g⁻¹ * g' : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ) :
    Submodule.ofFiniteIdele Λ g' ≤ Submodule.ofFiniteIdele Λ g := by
  intro z hz
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨((g⁻¹ * g' : (𝔸H)ˣ) : 𝔸H) * w, mul_mem_finiteAdeleBox hΛ h hw, ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [← hwz, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]

theorem smul_mem_ofFiniteIdele_of_smul_inv_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g g' : (𝔸H)ˣ) (c : ℚ) (h : c • ((g'⁻¹ * g : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ)
    {z : ℍ[ℚ, a, b]} (hz : z ∈ Submodule.ofFiniteIdele Λ g) : c • z ∈ Submodule.ofFiniteIdele Λ g' := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨(c • ((g'⁻¹ * g : (𝔸H)ˣ) : 𝔸H)) * w, mul_mem_finiteAdeleBox hΛ h hw, ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [smul_mul_assoc, mul_smul_comm, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left, hwz,
    TensorProduct.smul_tmul']

theorem mem_ofFiniteIdele_mul_mul_of_mem_of_eq_smul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x n m' : (𝔸H)ˣ) (N q : ℕ) (hcop : Nat.Coprime N q)
    (h4 : ((N : ℕ) : ℚ) • ((m'⁻¹ * n : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ)
    (h6 : ((q : ℕ) : ℚ) • (((n * n)⁻¹ : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ)
    (h8 : ((q : ℕ) : ℚ) • ((m'⁻¹ * n⁻¹ * m' : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ)
    {z y : ℍ[ℚ, a, b]} (hz : z ∈ Submodule.ofFiniteIdele Λ (x * m')) (hy : y ∈ Submodule.ofFiniteIdele Λ x)
    (hzy : z = ((q : ℕ) : ℚ) • y) :
    z ∈ Submodule.ofFiniteIdele Λ (x * n * m') := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz hy ⊢
  obtain ⟨w₁, hw₁, hw₁z⟩ := hz
  obtain ⟨w₂, hw₂, hw₂y⟩ := hy
  rw [AddMonoidHom.coe_mulLeft] at hw₁z hw₂y ⊢

  set w : 𝔸H := (((x * n * m')⁻¹ : (𝔸H)ˣ) : 𝔸H) * (z ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) with hw
  refine ⟨w, ?_, by rw [hw, Units.mul_inv_cancel_left]⟩

  have hq : ((q : ℕ) : ℚ) • w ∈ Submodule.finiteAdeleBox Λ := by
    have e1 : w = ((m'⁻¹ * n⁻¹ * m' : (𝔸H)ˣ) : 𝔸H) * w₁ := by
      rw [hw, ← hw₁z, ← mul_assoc, ← Units.val_mul]
      congr 2
      group
    rw [e1, ← smul_mul_assoc]
    exact mul_mem_finiteAdeleBox hΛ h8 hw₁

  have hN : ((N : ℕ) : ℚ) • w ∈ Submodule.finiteAdeleBox Λ := by
    have e2 : z ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) = ((q : ℕ) : ℚ) • ((x : 𝔸H) * w₂) := by
      rw [hw₂y, TensorProduct.smul_tmul', ← hzy]
    have e3 : w = ((q : ℕ) : ℚ) • (((m'⁻¹ * n⁻¹ : (𝔸H)ˣ) : 𝔸H) * w₂) := by
      rw [hw, e2, mul_smul_comm, ← mul_assoc, ← Units.val_mul]
      congr 3
      group
    have eBC : ((m'⁻¹ * n : (𝔸H)ˣ) : 𝔸H) * (((n * n)⁻¹ : (𝔸H)ˣ) : 𝔸H) = ((m'⁻¹ * n⁻¹ : (𝔸H)ˣ) : 𝔸H) := by
      rw [← Units.val_mul]
      congr 1
      group
    have hmem : ((((N : ℕ) : ℚ) • ((m'⁻¹ * n : (𝔸H)ˣ) : 𝔸H)) * (((q : ℕ) : ℚ) • (((n * n)⁻¹ : (𝔸H)ˣ) : 𝔸H))) * w₂ ∈
        Submodule.finiteAdeleBox Λ :=
      mul_mem_finiteAdeleBox hΛ (mul_mem_finiteAdeleBox hΛ h4 h6) hw₂
    rw [e3]
    convert hmem using 1
    rw [smul_mul_smul_comm, eBC, smul_mul_assoc, mul_smul]

  obtain ⟨u, v, huv⟩ : IsCoprime (N : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hone : (u : ℚ) * (N : ℕ) + (v : ℚ) * (q : ℕ) = 1 := by
    have := congrArg (fun t : ℤ => (t : ℚ)) huv
    push_cast at this
    exact this
  have hdecomp : w = (u : ℚ) • (((N : ℕ) : ℚ) • w) + (v : ℚ) • (((q : ℕ) : ℚ) • w) := by
    rw [smul_smul, smul_smul, ← add_smul, hone, one_smul]
  rw [hdecomp]
  exact add_mem (intCast_smul_mem_finiteAdeleBox hN u) (intCast_smul_mem_finiteAdeleBox hq v)

theorem mem_star_image_smul_iff (d : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) (u : ℍ[ℚ, a, b]) :
    u ∈ star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ↔ ∃ z ∈ I, u = star ((d : ℍ[ℚ, a, b]) * z) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w d I).mp hw
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(d : ℍ[ℚ, a, b]) * z, (Submodule.mem_smul_pointwise_iff_exists _ d I).mpr ⟨z, hz, rfl⟩, rfl⟩

theorem star_image_inter_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x n m' : (𝔸H)ˣ) (N q : ℕ) (hq0 : q ≠ 0) (hcop : Nat.Coprime N q)
    (h4 : ((N : ℕ) : ℚ) • ((m'⁻¹ * n : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ)
    (h5 : ((q : ℕ) : ℚ)⁻¹ • ((n * m' : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ)
    (h6 : ((q : ℕ) : ℚ) • (((n * n)⁻¹ : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ)
    (h7 : ((m'⁻¹ * n * m' : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ)
    (h8 : ((q : ℕ) : ℚ) • ((m'⁻¹ * n⁻¹ * m' : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ)
    (d : (ℍ[ℚ, a, b])ˣ) :
    star '' ((d • Submodule.ofFiniteIdele Λ (x * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ∩
      (· * ((q : ℕ) : ℍ[ℚ, a, b])) '' (star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) =
    star '' ((d • Submodule.ofFiniteIdele Λ (x * n * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  have hqQ : ((q : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq0

  have hstarq : ∀ y : ℍ[ℚ, a, b],
      star ((d : ℍ[ℚ, a, b]) * (((q : ℕ) : ℚ) • y)) = star ((d : ℍ[ℚ, a, b]) * y) * ((q : ℕ) : ℍ[ℚ, a, b]) := by
    intro y
    rw [mul_smul_comm, QuaternionAlgebra.star_smul, Algebra.smul_def, Algebra.commutes]
    simp
  ext u
  constructor
  · rintro ⟨hu1, ⟨u', hu', rfl⟩⟩
    obtain ⟨z, hz, hzu⟩ := (mem_star_image_smul_iff d _ _).mp hu1
    obtain ⟨y, hy, rfl⟩ := (mem_star_image_smul_iff d _ _).mp hu'

    have hzq : z = ((q : ℕ) : ℚ) • y := by
      have h1 : star ((d : ℍ[ℚ, a, b]) * z) = star ((d : ℍ[ℚ, a, b]) * (((q : ℕ) : ℚ) • y)) := by
        rw [← hzu, hstarq]
      have h2 : (d : ℍ[ℚ, a, b]) * z = (d : ℍ[ℚ, a, b]) * (((q : ℕ) : ℚ) • y) := star_injective h1
      exact (Units.mul_right_inj d).mp h2
    have hmem : z ∈ Submodule.ofFiniteIdele Λ (x * n * m') :=
      mem_ofFiniteIdele_mul_mul_of_mem_of_eq_smul hΛ x n m' N q hcop h4 h6 h8 hz hy hzq
    change star ((d : ℍ[ℚ, a, b]) * y) * ((q : ℕ) : ℍ[ℚ, a, b]) ∈ _
    rw [← hstarq, ← hzq]
    exact (mem_star_image_smul_iff d _ _).mpr ⟨z, hmem, rfl⟩
  · intro hu
    obtain ⟨z, hz, rfl⟩ := (mem_star_image_smul_iff d _ _).mp hu
    refine ⟨?_, ?_⟩
    ·
      have hle : Submodule.ofFiniteIdele Λ (x * n * m') ≤ Submodule.ofFiniteIdele Λ (x * m') := by
        refine ofFiniteIdele_le_of_inv_mul_mem hΛ (x * m') (x * n * m') ?_
        have : (x * m')⁻¹ * (x * n * m') = m'⁻¹ * n * m' := by group
        rw [this]; exact h7
      exact (mem_star_image_smul_iff d _ _).mpr ⟨z, hle hz, rfl⟩
    ·
      have hy : ((q : ℕ) : ℚ)⁻¹ • z ∈ Submodule.ofFiniteIdele Λ x := by
        refine smul_mem_ofFiniteIdele_of_smul_inv_mul_mem hΛ (x * n * m') x _ ?_ hz
        have : x⁻¹ * (x * n * m') = n * m' := by group
        rw [this]; exact h5
      refine ⟨star ((d : ℍ[ℚ, a, b]) * (((q : ℕ) : ℚ)⁻¹ • z)), (mem_star_image_smul_iff d _ _).mpr ⟨_, hy, rfl⟩, ?_⟩
      show star ((d : ℍ[ℚ, a, b]) * (((q : ℕ) : ℚ)⁻¹ • z)) * ((q : ℕ) : ℍ[ℚ, a, b]) = star ((d : ℍ[ℚ, a, b]) * z)
      rw [← hstarq, smul_smul, mul_inv_cancel₀ hqQ, one_smul]

end Adelic

section Points

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

abbrev Pt (W : WeierstrassCurve κ) := W.toAffine.Point

open WeierstrassCurve in
theorem infinite_point (W : WeierstrassCurve κ) [W.IsElliptic] : Infinite (Pt W) := by
  have hy : ∀ x : κ, ∃ y : κ, W.toAffine.Nonsingular x y := by
    intro x
    have hdeg : (W.toAffine.polynomial.map (Polynomial.evalRingHom x)).degree ≠ 0 := by
      rw [WeierstrassCurve.Affine.monic_polynomial.degree_map, WeierstrassCurve.Affine.degree_polynomial]
      norm_num
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, (W.toAffine.equation_iff_nonsingular).mp ?_⟩
    rw [Polynomial.IsRoot.def, Polynomial.map_evalRingHom_eval] at hy
    exact hy
  choose f hf using hy
  refine Infinite.of_injective (fun x : κ => (Affine.Point.some x (f x) (hf x) : Pt W)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

variable {W₁ W₂ : WeierstrassCurve κ} [W₁.IsElliptic] [W₂.IsElliptic]

theorem sub_mem_rationalHomSet {α β : Pt W₁ →+ Pt W₂}
    (hα : α ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) (hβ : β ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) :
    α - β ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact WeierstrassCurve.add_mem_rationalHomSet κ W₁ W₂ hα (WeierstrassCurve.neg_mem_rationalHomSet κ W₁ W₂ hβ)

theorem zsmul_mem_rationalHomSet {α : Pt W₁ →+ Pt W₂}
    (hα : α ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) (c : ℤ) :
    c • α ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂ := by
  induction c using Int.induction_on with
  | zero => rw [zero_zsmul]; exact WeierstrassCurve.zero_mem_rationalHomSet κ W₁ W₂
  | succ n ih => rw [add_zsmul, one_zsmul]; exact WeierstrassCurve.add_mem_rationalHomSet κ W₁ W₂ ih hα
  | pred n ih => rw [sub_zsmul, one_zsmul]; exact sub_mem_rationalHomSet ih hα

theorem nsmul_mem_rationalHomSet {α : Pt W₁ →+ Pt W₂}
    (hα : α ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) (c : ℕ) :
    c • α ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂ := by
  rw [← natCast_zsmul]; exact zsmul_mem_rationalHomSet hα c

theorem finite_torsion (W : WeierstrassCurve κ) [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) (hnk : (n : κ) ≠ 0) :
    {P : Pt W | (n : ℤ) • P = 0}.Finite := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (Pt W) (n : ℤ)) = n ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W hnk
  haveI : Finite (Submodule.torsionBy ℤ (Pt W) (n : ℤ)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]; exact pow_ne_zero 2 hn
  have : {P : Pt W | (n : ℤ) • P = 0} = ((Submodule.torsionBy ℤ (Pt W) (n : ℤ)) : Set (Pt W)) := by
    ext P; exact (Submodule.mem_torsionBy_iff _ _).symm
  rw [this]
  exact Set.toFinite _

theorem eq_zero_of_finite_range {α : Pt W₁ →+ Pt W₂}
    (hα : α ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) (hfin : (Set.range α).Finite) : α = 0 := by
  by_contra hα0
  have hsurj : Function.Surjective α := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hα hα0
  haveI := infinite_point W₂
  exact Set.infinite_univ (hfin.subset fun P _ => by
    obtain ⟨P', hP'⟩ := hsurj P
    exact ⟨P', hP'⟩)

theorem eq_zero_of_nsmul_eq_zero {α : Pt W₁ →+ Pt W₂}
    (hα : α ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) {n : ℕ} (hn : n ≠ 0) (hnk : (n : κ) ≠ 0)
    (h : n • α = 0) : α = 0 := by
  refine eq_zero_of_finite_range hα ((finite_torsion W₂ hn hnk).subset ?_)
  rintro _ ⟨P, rfl⟩
  have := DFunLike.congr_fun h P
  rw [AddMonoidHom.nsmul_apply, AddMonoidHom.zero_apply] at this
  change (n : ℤ) • α P = 0
  rw [natCast_zsmul]; exact this

theorem nsmul_id_ne_zero (W : WeierstrassCurve κ) [W.IsElliptic] {ℓ : ℕ} (hℓ : ℓ ≠ 0) (hℓκ : (ℓ : κ) ≠ 0) :
    (ℓ • AddMonoidHom.id (Pt W)) ≠ 0 := by
  intro h
  have h0 := eq_zero_of_nsmul_eq_zero (WeierstrassCurve.id_mem_rationalHomSet κ W) hℓ hℓκ h
  haveI := infinite_point W
  obtain ⟨P, hP⟩ := exists_ne (0 : Pt W)
  exact hP (by
    first
      | simpa using DFunLike.congr_fun h0 P
      | (have h' := DFunLike.congr_fun h0 P; simp at h'; exact h')
      | exact DFunLike.congr_fun h0 P)

theorem natCast_zsmul_eq_zero_of_mem_of_card {U : AddSubgroup (Pt W₁)} {ℓ : ℕ} (hU : Nat.card U = ℓ)
    {P : Pt W₁} (hP : P ∈ U) : (ℓ : ℤ) • P = 0 := by
  have h := card_nsmul_eq_zero' (x := (⟨P, hP⟩ : U))
  rw [hU] at h
  rw [natCast_zsmul]
  exact congrArg Subtype.val h

theorem univ_of_dualPair (W W'' V : WeierstrassCurve κ) [W.IsElliptic] [W''.IsElliptic] [V.IsElliptic]
    (ψE : Pt W →+ Pt W'') (hψE : ψE ∈ WeierstrassCurve.rationalHomSet κ W W'')
    (ψE' : Pt W'' →+ Pt W) (hψE' : ψE' ∈ WeierstrassCurve.rationalHomSet κ W'' W)
    (L : ℕ) (hLκ : (L : κ) ≠ 0)
    (hd1 : ψE'.comp ψE = (L : ℕ) • AddMonoidHom.id _) (hd2 : ψE.comp ψE' = (L : ℕ) • AddMonoidHom.id _)
    (β : Pt W →+ Pt V) (hβ : β ∈ WeierstrassCurve.rationalHomSet κ W V) (hβker : ∀ T ∈ ψE.ker, β T = 0) :
    ∃ γ : Pt W'' →+ Pt V, γ ∈ WeierstrassCurve.rationalHomSet κ W'' V ∧ β = γ.comp ψE := by
  have hL0 : L ≠ 0 := by rintro rfl; exact hLκ (by simp)
  have hβψ : β.comp ψE' ∈ WeierstrassCurve.rationalHomSet κ W'' V :=
    WeierstrassCurve.comp_mem_rationalHomSet κ W'' W V hψE' hβ
  have hkill : ∀ P : Pt W'', (L : ℤ) • P = 0 → (β.comp ψE') P = 0 := by
    intro P hP
    apply hβker
    rw [AddMonoidHom.mem_ker]
    have h2 := DFunLike.congr_fun hd2 P
    rw [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, ← natCast_zsmul, hP] at h2
    exact h2
  obtain ⟨γ, hγ, hγeq⟩ : ∃ γ : Pt W'' →+ Pt V,
      γ ∈ WeierstrassCurve.rationalHomSet κ W'' V ∧ ∀ P : Pt W'', (β.comp ψE') P = (L : ℤ) • γ P :=
    WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W'' V hLκ hβψ hkill
  refine ⟨γ, hγ, ?_⟩
  have hdiff : β - γ.comp ψE ∈ WeierstrassCurve.rationalHomSet κ W V :=
    sub_mem_rationalHomSet hβ (WeierstrassCurve.comp_mem_rationalHomSet κ W W'' V hψE hγ)
  have hzero : L • (β - γ.comp ψE) = 0 := by
    ext T
    have h1 := DFunLike.congr_fun hd1 T
    rw [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply] at h1
    have h3 := hγeq (ψE T)
    rw [AddMonoidHom.comp_apply, h1, map_nsmul] at h3
    rw [AddMonoidHom.nsmul_apply, AddMonoidHom.zero_apply, AddMonoidHom.sub_apply, smul_sub, sub_eq_zero,
      AddMonoidHom.comp_apply, h3, natCast_zsmul]
  exact sub_eq_zero.mp (eq_zero_of_nsmul_eq_zero hdiff hL0 hLκ hzero)

end Points

section LevelData

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem mem_zmultiples_add_of_coprime {G : Type*} [AddCommGroup G] {N q : ℕ} (hcop : Nat.Coprime N q)
    {u w : G} (hu : N • u = 0) (hw : q • w = 0) :
    u ∈ AddSubgroup.zmultiples (u + w) ∧ w ∈ AddSubgroup.zmultiples (u + w) := by
  obtain ⟨α, β, hαβ⟩ : IsCoprime (N : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hu' : (N : ℤ) • u = 0 := by rw [natCast_zsmul]; exact hu
  have hw' : (q : ℤ) • w = 0 := by rw [natCast_zsmul]; exact hw
  have hu1 : (β * (q : ℤ)) • u = u := by
    have h1 : (α * (N : ℤ) + β * (q : ℤ)) • u = u := by rw [hαβ, one_smul]
    rwa [add_smul, mul_smul α, hu', smul_zero, zero_add] at h1
  have hw1 : (α * (N : ℤ)) • w = w := by
    have h1 : (α * (N : ℤ) + β * (q : ℤ)) • w = w := by rw [hαβ, one_smul]
    rwa [add_smul, mul_smul β, hw', smul_zero, add_zero] at h1
  constructor
  ·
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨β * q, ?_⟩
    rw [smul_add, hu1, mul_smul, hw', smul_zero, add_zero]
  · refine AddSubgroup.mem_zmultiples_iff.mpr ⟨α * N, ?_⟩
    rw [smul_add, hw1, mul_smul, hu', smul_zero, zero_add]

theorem exists_torsion_not_mem (W : WeierstrassCurve κ) [W.IsElliptic] {q : ℕ} (hq : q.Prime) (hqκ : (q : κ) ≠ 0)
    (Q : Pt W) (hQ : addOrderOf Q = q) :
    ∃ t : Pt W, q • t = 0 ∧ t ∉ AddSubgroup.zmultiples Q := by
  by_contra hcon
  have hcon' : ∀ t : Pt W, q • t = 0 → t ∈ AddSubgroup.zmultiples Q := by
    intro t ht
    by_contra h
    exact hcon ⟨t, ht, h⟩
  have hcard : Nat.card (Submodule.torsionBy ℤ (Pt W) (q : ℤ)) = q ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W hqκ
  haveI : Finite (AddSubgroup.zmultiples Q) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zmultiples, hQ]; exact hq.ne_zero
  have hmemQ : ∀ P : Submodule.torsionBy ℤ (Pt W) (q : ℤ), (P : Pt W) ∈ AddSubgroup.zmultiples Q := by
    intro P
    refine hcon' P.1 ?_
    have := (Submodule.mem_torsionBy_iff (q : ℤ) P.1).mp P.2
    rwa [natCast_zsmul] at this
  have hle : Nat.card (Submodule.torsionBy ℤ (Pt W) (q : ℤ)) ≤ Nat.card (AddSubgroup.zmultiples Q) := by
    refine Nat.card_le_card_of_injective (fun P => (⟨P.1, hmemQ P⟩ : AddSubgroup.zmultiples Q)) ?_
    intro P P' h
    apply Subtype.ext
    have := congrArg (fun s : AddSubgroup.zmultiples Q => (s : Pt W)) h
    exact this
  rw [hcard, Nat.card_zmultiples, hQ, pow_two] at hle
  have h2 : 2 ≤ q := hq.two_le
  have h3 : q * q ≤ q * 1 := by simpa using hle
  have h4 : q ≤ 1 := Nat.le_of_mul_le_mul_left h3 (by omega)
  omega

theorem torsion_mem_sup (W : WeierstrassCurve κ) [W.IsElliptic] {q : ℕ} (hq : q.Prime) (hqκ : (q : κ) ≠ 0)
    (Q : Pt W) (hQ : addOrderOf Q = q) (t : Pt W) (ht : q • t = 0) (htQ : t ∉ AddSubgroup.zmultiples Q)
    (T : Pt W) (hT : q • T = 0) :
    ∃ i j : ℤ, T = i • Q + j • t := by
  haveI : Fact q.Prime := ⟨hq⟩

  set Tq : AddSubgroup (Pt W) := (Submodule.torsionBy ℤ (Pt W) (q : ℤ)).toAddSubgroup with hTq
  have hmemTq : ∀ P : Pt W, P ∈ Tq ↔ q • P = 0 := by
    intro P
    rw [hTq, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, ← natCast_zsmul]
  have hcardTq : Nat.card Tq = q ^ 2 := by
    rw [hTq]
    exact WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W hqκ
  haveI hfin : Finite Tq := Nat.finite_of_card_ne_zero (by rw [hcardTq]; exact pow_ne_zero 2 hq.ne_zero)
  have hqQ : q • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  set H : AddSubgroup (Pt W) := AddSubgroup.zmultiples Q ⊔ AddSubgroup.zmultiples t with hH
  have hHle : H ≤ Tq := by
    rw [hH, sup_le_iff]
    constructor
    · rw [AddSubgroup.zmultiples_le]; exact (hmemTq Q).mpr hqQ
    · rw [AddSubgroup.zmultiples_le]; exact (hmemTq t).mpr ht
  haveI : Finite H := Finite.of_injective (AddSubgroup.inclusion hHle) (AddSubgroup.inclusion_injective hHle)

  have hdvd : Nat.card H ∣ q ^ 2 := hcardTq ▸ AddSubgroup.card_dvd_of_le hHle
  obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  have hQle : AddSubgroup.zmultiples Q ≤ H := le_sup_left
  have hcardQ : Nat.card (AddSubgroup.zmultiples Q) = q := by rw [Nat.card_zmultiples, hQ]
  have hk2 : k = 2 := by
    interval_cases k
    ·
      exfalso
      have hq1 : q ∣ 1 := by
        have := AddSubgroup.card_dvd_of_le hQle
        rwa [hcardQ, hkH, pow_zero] at this
      exact hq.one_lt.ne' (Nat.dvd_one.mp hq1)
    ·
      exfalso
      rw [pow_one] at hkH
      have heq : AddSubgroup.zmultiples Q = H :=
        AddSubgroup.eq_of_le_of_card_ge hQle (by rw [hkH, hcardQ])
      have htH : t ∈ H := (le_sup_right : AddSubgroup.zmultiples t ≤ H) (AddSubgroup.mem_zmultiples t)
      rw [← heq] at htH
      exact htQ htH
    · rfl
  rw [hk2] at hkH
  have hHeq : H = Tq := AddSubgroup.eq_of_le_of_card_ge hHle (by rw [hkH, hcardTq])
  have hTH : T ∈ H := by rw [hHeq]; exact (hmemTq T).mpr hT
  rw [hH] at hTH
  obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hTH
  obtain ⟨i, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
  exact ⟨i, j, hyz.symm⟩

theorem level_data
    (W V : WeierstrassCurve κ) [W.IsElliptic] [V.IsElliptic]
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (hNqκ : ((N * q : ℕ) : κ) ≠ 0) (hqκ : ((q : ℕ) : κ) ≠ 0)
    (K : AddSubgroup (Pt W)) (gE : Pt W) (hgE : AddSubgroup.zmultiples gE = K) (hgEord : addOrderOf gE = N * q)
    (φ : Pt W →+ Pt V) (hφ : φ ∈ WeierstrassCurve.rationalHomSet κ W V)
    (hφker : φ.ker = AddSubgroup.zmultiples (N • gE)) (hφsurj : Function.Surjective φ) :
    ∃ (V₃ : WeierstrassCurve κ) (_ : V₃.IsElliptic) (ψ₃ : Pt V →+ Pt V₃)
      (_ : ψ₃ ∈ WeierstrassCurve.rationalHomSet κ V V₃)
      (ψ₃' : Pt V₃ →+ Pt V) (_ : ψ₃' ∈ WeierstrassCurve.rationalHomSet κ V₃ V)
      (_ : ψ₃'.comp ψ₃ = ((N * q : ℕ)) • AddMonoidHom.id _) (_ : ψ₃.comp ψ₃' = ((N * q : ℕ)) • AddMonoidHom.id _),
      IsAddCyclic ψ₃.ker ∧ Nat.card ψ₃.ker = N * q ∧
      (∀ T ∈ K, φ T ∈ ψ₃.ker) ∧ (∀ T : Pt W, q • T = 0 → φ T ∈ ψ₃.ker) ∧
      (∀ P : Pt W, ψ₃ (φ P) = 0 → ∃ (k : ℤ) (T' : Pt W), q • T' = 0 ∧ P = k • gE + T') ∧
      (∀ (V' : WeierstrassCurve κ) [V'.IsElliptic] (α : Pt V →+ Pt V'),
        α ∈ WeierstrassCurve.rationalHomSet κ V V' → ψ₃.ker ≤ α.ker →
          ∃ β ∈ WeierstrassCurve.rationalHomSet κ V₃ V', α = β.comp ψ₃) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hN0 : N ≠ 0 := NeZero.ne N
  have hcop : Nat.Coprime N q := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN |>.symm

  have hQord : addOrderOf (N • gE) = q := by
    rw [addOrderOf_nsmul' gE hN0, hgEord, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hN0)]

  obtain ⟨t, htq, htQ⟩ := exists_torsion_not_mem W hq hqκ (N • gE) hQord

  have hNu : N • φ gE = 0 := by
    rw [← map_nsmul]; exact (AddMonoidHom.mem_ker).mp (hφker ▸ AddSubgroup.mem_zmultiples (N • gE))
  have hqw : q • φ t = 0 := by rw [← map_nsmul, htq, map_zero]
  have hw0 : φ t ≠ 0 := by
    intro h
    exact htQ (hφker ▸ (AddMonoidHom.mem_ker).mpr h)

  have hordw : addOrderOf (φ t) = q := addOrderOf_eq_prime hqw hw0
  have hordu : addOrderOf (φ gE) = N := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hNu) ?_

    have ho : addOrderOf (φ gE) • gE ∈ φ.ker := by
      rw [AddMonoidHom.mem_ker, map_nsmul]; exact addOrderOf_nsmul_eq_zero _
    rw [hφker] at ho
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ho
    have h1 : ((addOrderOf (φ gE) : ℤ) - k * N) • gE = 0 := by
      rw [sub_smul, natCast_zsmul, ← hk, mul_smul, natCast_zsmul, sub_self]
    have h2 : ((N * q : ℕ) : ℤ) ∣ (addOrderOf (φ gE) : ℤ) - k * N := by
      rw [← hgEord]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
    have h3 : (N : ℤ) ∣ (addOrderOf (φ gE) : ℤ) := by
      have h4 : (N : ℤ) ∣ (addOrderOf (φ gE) : ℤ) - k * N := (Dvd.intro (q : ℤ) (by push_cast; ring)).trans h2
      have h5 : (N : ℤ) ∣ k * N := Dvd.intro_left _ rfl
      simpa using dvd_add h4 h5
    exact_mod_cast h3

  set C'' : AddSubgroup (Pt V) := AddSubgroup.zmultiples (φ gE + φ t) with hC''
  have hcardC : Nat.card C'' = N * q := by
    rw [hC'', Nat.card_zmultiples,
      (AddCommute.all _ _).addOrderOf_add_eq_mul_addOrderOf_of_coprime (by rw [hordu, hordw]; exact hcop), hordu, hordw]
  obtain ⟨hu_mem, hw_mem⟩ := mem_zmultiples_add_of_coprime hcop hNu hqw
  have hKmem : ∀ T ∈ K, φ T ∈ C'' := by
    intro T hT
    rw [← hgE] at hT
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ hu_mem k
  have htors : ∀ T : Pt W, q • T = 0 → φ T ∈ C'' := by
    intro T hT
    obtain ⟨i, j, rfl⟩ := torsion_mem_sup W hq hqκ (N • gE) hQord t htq htQ T hT
    have hφQ : φ (N • gE) = 0 := (AddMonoidHom.mem_ker).mp (hφker ▸ AddSubgroup.mem_zmultiples (N • gE))
    rw [map_add, map_zsmul, map_zsmul, hφQ, smul_zero, zero_add]
    exact AddSubgroup.zsmul_mem _ hw_mem j

  have hCκ : ((Nat.card C'' : ℕ) : κ) ≠ 0 := by rw [hcardC]; exact hNqκ
  obtain ⟨V₃, hV₃, ψ₃, hψ₃, hψ₃surj, hψ₃ker, hψ₃univ⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp V C'' hCκ
  haveI := hV₃
  have hψ₃ker' : ψ₃.ker = C'' := hψ₃ker

  have hid : ((N * q : ℕ) • AddMonoidHom.id (Pt V)) ∈ WeierstrassCurve.rationalHomSet κ V V :=
    nsmul_mem_rationalHomSet (WeierstrassCurve.id_mem_rationalHomSet κ V) (N * q)
  have hidker : C'' ≤ ((N * q : ℕ) • AddMonoidHom.id (Pt V)).ker := by
    intro P hP
    rw [AddMonoidHom.mem_ker, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, ← hcardC]
    exact congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨P, hP⟩ : C'')))
  obtain ⟨ψ₃', hψ₃', hdual⟩ := hψ₃univ V _ hid hidker
  have he1 : ψ₃'.comp ψ₃ = (N * q : ℕ) • AddMonoidHom.id _ := hdual.symm
  have he2 : ψ₃.comp ψ₃' = (N * q : ℕ) • AddMonoidHom.id _ := by
    ext P
    obtain ⟨R, rfl⟩ := hψ₃surj P
    have := DFunLike.congr_fun he1 R
    rw [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply] at this
    rw [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, this, map_nsmul]

  have hkerdesc : ∀ P : Pt W, ψ₃ (φ P) = 0 → ∃ (k : ℤ) (T' : Pt W), q • T' = 0 ∧ P = k • gE + T' := by
    intro P hP
    have hPC : φ P ∈ C'' := by rw [← hψ₃ker']; exact hP
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hPC
    have hdiff : P - k • (gE + t) ∈ φ.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, map_zsmul, map_add, hk, sub_self]
    rw [hφker] at hdiff
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hdiff
    refine ⟨k + j * N, k • t, ?_, ?_⟩
    · rw [smul_comm, htq, smul_zero]
    · have : P = k • (gE + t) + j • (N • gE) := by rw [hj, add_sub_cancel]
      rw [this, smul_add, add_smul, mul_smul, natCast_zsmul]
      abel
  refine ⟨V₃, hV₃, ψ₃, hψ₃, ψ₃', hψ₃', he1, he2, ?_, ?_, ?_, ?_, hkerdesc, ?_⟩
  · have h : IsAddCyclic C'' := by rw [hC'']; infer_instance
    rw [← hψ₃ker'] at h
    exact h
  · have h := hcardC
    rw [← hψ₃ker'] at h
    exact h
  · intro T hT
    have h := hKmem T hT
    rw [← hψ₃ker'] at h
    exact h
  · intro T hT
    have h := htors T hT
    rw [← hψ₃ker'] at h
    exact h
  · intro V' _ α hα hle
    refine hψ₃univ V' α hα ?_
    intro P hP
    apply hle
    show ψ₃ P = 0
    have h : P ∈ C'' := hP
    rw [← hψ₃ker'] at h
    exact h

end LevelData

section Heart

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem coe_nsmul_apply {M : Type*} [AddCommGroup M] (S : Subring (AddMonoid.End M)) (s : S) (n : ℕ) (m : M) :
    ((n • s : S) : AddMonoid.End M) m = n • (s : AddMonoid.End M) m := by
  rw [AddSubmonoidClass.coe_nsmul]
  rfl

theorem heart2
    (X₁ W W'' V V₃ : WeierstrassCurve κ) [X₁.IsElliptic] [W.IsElliptic] [W''.IsElliptic] [V.IsElliptic] [V₃.IsElliptic]
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]) (hθ₁ : Function.Injective θ₁)
    (χ : Pt X₁ →+ Pt W) (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0)
    (ψE : Pt W →+ Pt W'') (hψE : ψE ∈ WeierstrassCurve.rationalHomSet κ W W'')
    (ψE' : Pt W'' →+ Pt W) (hψE' : ψE' ∈ WeierstrassCurve.rationalHomSet κ W'' W)
    (L : ℕ) (hLκ : (L : κ) ≠ 0)
    (hd1 : ψE'.comp ψE = (L : ℕ) • AddMonoidHom.id _) (hd2 : ψE.comp ψE' = (L : ℕ) • AddMonoidHom.id _)
    (gE : Pt W) (hgEker : ψE gE = 0) (Q : Pt W) (hQker : ψE Q = 0)
    (q : ℕ) (hqκ : (q : κ) ≠ 0)
    (φ : Pt W →+ Pt V) (hφ : φ ∈ WeierstrassCurve.rationalHomSet κ W V) (hφsurj : Function.Surjective φ)
    (hφuniv : ∀ (V' : WeierstrassCurve κ) [V'.IsElliptic] (α : Pt W →+ Pt V'),
        α ∈ WeierstrassCurve.rationalHomSet κ W V' → α Q = 0 →
          ∃ γ : Pt V →+ Pt V', γ ∈ WeierstrassCurve.rationalHomSet κ V V' ∧ α = γ.comp φ)
    (ψ₃ : Pt V →+ Pt V₃) (hψ₃ : ψ₃ ∈ WeierstrassCurve.rationalHomSet κ V V₃)
    (hKmem : ∀ T ∈ ψE.ker, φ T ∈ ψ₃.ker) (htors : ∀ T : Pt W, q • T = 0 → φ T ∈ ψ₃.ker)
    (hkerdesc : ∀ P : Pt W, ψ₃ (φ P) = 0 → ∃ (k : ℤ) (T' : Pt W), q • T' = 0 ∧ P = k • gE + T')
    (hψ₃univ : ∀ (V' : WeierstrassCurve κ) [V'.IsElliptic] (α : Pt V →+ Pt V'),
        α ∈ WeierstrassCurve.rationalHomSet κ V V' → ψ₃.ker ≤ α.ker →
          ∃ β ∈ WeierstrassCurve.rationalHomSet κ V₃ V', α = β.comp ψ₃) :
    θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ V₃ (ψ₃.comp (φ.comp χ)) =
      θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W'' (ψE.comp χ) ∩
        (· * ((q : ℕ) : ℍ[ℚ, a, b])) '' (θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ) := by
  classical
  have hsurjχ : Function.Surjective χ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ hχ0

  have hunivE := univ_of_dualPair W W'' X₁ ψE hψE ψE' hψE' L hLκ hd1 hd2
  have hunivC : ∀ α : Pt W →+ Pt X₁, α ∈ WeierstrassCurve.rationalHomSet κ W X₁ →
      (∀ T ∈ ψE.ker, α T = 0) → (∀ T : Pt W, q • T = 0 → α T = 0) →
        ∃ ρ ∈ WeierstrassCurve.rationalHomSet κ V₃ X₁, α = ρ.comp (ψ₃.comp φ) := by
    intro α hα hαK hαq
    obtain ⟨γ, hγ, hαγ⟩ := hφuniv X₁ α hα (hαK Q hQker)
    have hγker : ψ₃.ker ≤ γ.ker := by
      intro v hv
      obtain ⟨P, rfl⟩ := hφsurj v
      obtain ⟨k, T', hT', hP⟩ := hkerdesc P hv
      rw [AddMonoidHom.mem_ker, show γ (φ P) = α P by rw [hαγ]; rfl, hP, map_add, map_zsmul, hαK gE hgEker,
        smul_zero, zero_add, hαq T' hT']
    obtain ⟨ρ, hρ, hγρ⟩ := hψ₃univ X₁ γ hγ hγker
    refine ⟨ρ, hρ, ?_⟩
    rw [hαγ, hγρ]
    rfl

  have hθq : ∀ s : ↥(WeierstrassCurve.rationalEndSubring κ X₁), θ₁ (q • s) = θ₁ s * ((q : ℕ) : ℍ[ℚ, a, b]) := by
    intro s; rw [map_nsmul, nsmul_eq_mul, Nat.cast_comm]
  ext u
  constructor
  · rintro ⟨s, ⟨ρ, hρ, hs⟩, rfl⟩

    set α : Pt W →+ Pt X₁ := (ρ.comp ψ₃).comp φ with hαdef
    have hα : α ∈ WeierstrassCurve.rationalHomSet κ W X₁ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ W V X₁ hφ (WeierstrassCurve.comp_mem_rationalHomSet κ V V₃ X₁ hψ₃ hρ)
    have hsα : s.1 = α.comp χ := by rw [hs, hαdef]; rfl
    refine ⟨?_, ?_⟩
    ·
      have hαK : ∀ T ∈ ψE.ker, α T = 0 := by
        intro T hT
        have := hKmem T hT
        rw [AddMonoidHom.mem_ker] at this
        show ρ (ψ₃ (φ T)) = 0
        rw [this]
        exact map_zero ρ
      obtain ⟨γ, hγ, hαγ⟩ := hunivE α hα hαK
      refine ⟨s, ⟨γ, hγ, ?_⟩, rfl⟩
      rw [hsα, hαγ]
      rfl
    ·
      have hαq : ∀ P : Pt W, (q : ℤ) • P = 0 → α P = 0 := by
        intro P hP
        have := htors P (by rw [← natCast_zsmul]; exact hP)
        rw [AddMonoidHom.mem_ker] at this
        show ρ (ψ₃ (φ P)) = 0
        rw [this]
        exact map_zero ρ
      obtain ⟨β, hβ, hβeq⟩ :=
        WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W X₁ hqκ hα hαq
      have hmem' : β.comp χ ∈ WeierstrassCurve.rationalEndSubring κ X₁ :=
        Subring.subset_closure (WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W X₁ hχ hβ)
      set s' : ↥(WeierstrassCurve.rationalEndSubring κ X₁) := ⟨β.comp χ, hmem'⟩ with hs'
      have hs'K : s' ∈ WeierstrassCurve.kernelIdealSet κ X₁ W χ := ⟨β, hβ, rfl⟩
      have hss' : s = q • s' := by
        apply Subtype.ext
        apply DFunLike.ext
        intro P
        rw [coe_nsmul_apply, hsα]
        show α (χ P) = q • β (χ P)
        exact (hβeq (χ P)).trans (natCast_zsmul _ q)
      refine ⟨θ₁ s', ⟨s', hs'K, rfl⟩, ?_⟩
      show θ₁ s' * ((q : ℕ) : ℍ[ℚ, a, b]) = θ₁ s
      rw [hss', hθq]
  · rintro ⟨⟨s₁, ⟨ρ₁, hρ₁, hs₁⟩, hu₁⟩, ⟨u₂, ⟨s₂, ⟨ρ₂, hρ₂, hs₂⟩, rfl⟩, hu₂⟩⟩

    have h12 : s₁ = q • s₂ := by
      apply hθ₁
      rw [hθq, hu₁]
      exact hu₂.symm

    set α : Pt W →+ Pt X₁ := ρ₁.comp ψE with hαdef
    have hα : α ∈ WeierstrassCurve.rationalHomSet κ W X₁ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ W W'' X₁ hψE hρ₁
    have hαχ : ∀ P : Pt X₁, α (χ P) = q • ρ₂ (χ P) := by
      intro P
      have h := congrArg (fun e : ↥(WeierstrassCurve.rationalEndSubring κ X₁) => e.1 P) h12
      beta_reduce at h
      rw [coe_nsmul_apply, hs₁, hs₂] at h
      exact h
    have hαq' : ∀ T : Pt W, α T = q • ρ₂ T := by
      intro T
      obtain ⟨P, rfl⟩ := hsurjχ T
      exact hαχ P
    have hαK : ∀ T ∈ ψE.ker, α T = 0 := by
      intro T hT
      rw [AddMonoidHom.mem_ker] at hT
      show ρ₁ (ψE T) = 0
      rw [hT]
      exact map_zero ρ₁
    have hαq : ∀ T : Pt W, q • T = 0 → α T = 0 := by
      intro T hT
      have h0 : ρ₂ (q • T) = 0 := by rw [hT]; exact map_zero ρ₂
      rw [hαq', ← map_nsmul]
      exact h0
    obtain ⟨ρ, hρ, hαρ⟩ := hunivC α hα hαK hαq
    refine ⟨s₁, ⟨ρ, hρ, ?_⟩, hu₁⟩
    have e := congrArg (fun f : Pt W →+ Pt X₁ => f.comp χ) hαρ
    rw [hs₁]
    exact e

theorem heart1
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime] (hqN : ¬ q ∣ N) (hq'q : ¬ q' ∣ N * q)
    (m' n : (𝔸H)ˣ)
    (h1 : ((n : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ₁)
    (h2 : ((q : ℕ) : ℚ) • ((n⁻¹ : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ₁)
    (h3 : ((n⁻¹ * m' : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ₁)
    (h4 : ((N : ℕ) : ℚ) • ((m'⁻¹ * n : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ₁)
    (x : (𝔸H)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : X₁.toAffine.Point →+ W.toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (W'' : WeierstrassCurve κ) [W''.IsElliptic] (ψ : W.toAffine.Point →+ W''.toAffine.Point)
    (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W'')
    (ψ' : W''.toAffine.Point →+ W.toAffine.Point) (hψ' : ψ' ∈ WeierstrassCurve.rationalHomSet κ W'' W)
    (hψ'ψ : ψ'.comp ψ = ((N * q) : ℕ) • AddMonoidHom.id _) (hψψ' : ψ.comp ψ' = ((N * q) : ℕ) • AddMonoidHom.id _)
    (hK'' : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W'' (ψ.comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (g : W.toAffine.Point) (hg : AddSubgroup.zmultiples g = ψ.ker)
    (V : WeierstrassCurve κ) [V.IsElliptic] (φ : W.toAffine.Point →+ V.toAffine.Point)
    (hφ : φ ∈ WeierstrassCurve.rationalHomSet κ W V) (hφker : φ.ker = AddSubgroup.zmultiples (N • g))
    (hφuniv : ∀ (V' : WeierstrassCurve κ) [V'.IsElliptic] (α : W.toAffine.Point →+ V'.toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet κ W V' → α (N • g) = 0 →
          ∃ γ : V.toAffine.Point →+ V'.toAffine.Point,
            γ ∈ WeierstrassCurve.rationalHomSet κ V V' ∧ α = γ.comp φ) :
    θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ V (φ.comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * n) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  have hqpos : 0 < q := NeZero.pos q
  have hdiv : N * q / q = N := Nat.mul_div_cancel N hqpos
  have hML : q ∣ N * q := dvd_mul_left q N
  have hcop : Nat.Coprime q (N * q / q) := by
    rw [hdiv]; exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqN
  have h4' : ((N * q / q : ℕ) : ℚ) • ((m'⁻¹ * n : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox Λ₁ := by
    rw [hdiv]; exact h4
  have hπker : ∀ T : W.toAffine.Point, T ∈ φ.ker ↔ ∃ S ∈ ψ.ker, (N * q / q) • S = T := by
    intro T
    rw [hdiv, hφker, ← hg]
    constructor
    · intro hT
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
      exact ⟨k • g, AddSubgroup.mem_zmultiples_iff.mpr ⟨k, rfl⟩, smul_comm N k g⟩
    · rintro ⟨S, hS, rfl⟩
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hS
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, smul_comm k N g⟩
  have hπuniv : ∀ (V' : WeierstrassCurve κ) [V'.IsElliptic] (α : W.toAffine.Point →+ V'.toAffine.Point),
      α ∈ WeierstrassCurve.rationalHomSet κ W V' → φ.ker ≤ α.ker →
        ∃ β ∈ WeierstrassCurve.rationalHomSet κ V V', α = β.comp φ := by
    intro V' _ α hα hle
    have hQ0 : α (N • g) = 0 := by
      have : N • g ∈ α.ker := hle (by rw [hφker]; exact AddSubgroup.mem_zmultiples _)
      exact this
    obtain ⟨γ, hγ, h⟩ := hφuniv V' α hα hQ0
    exact ⟨γ, hγ, h⟩
  exact CerednikDrinfeld.image_kernelIdealSet_comp_eq_of_ker_eq_div_nsmul_ker_of_coprime q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁
    hθ₁ hθ₁Λ x W χ hχ hχ0 d hK (N * q) hq'q m' W'' ψ hψ ψ' hψ' hψ'ψ hψψ' hK'' q hML hcop n h1 h3 h2 h4' V φ hφ
    hπker hπuniv

end Heart

section Last

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem exists_zmultiples_eq {G : Type*} [AddCommGroup G] (C : AddSubgroup G) (hC : IsAddCyclic C) (n : ℕ)
    (hn : Nat.card C = n) : ∃ Q : G, AddSubgroup.zmultiples Q = C ∧ addOrderOf Q = n := by
  obtain ⟨Q, hQ⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top C).mp hC
  refine ⟨Q, hQ, ?_⟩
  rw [← Nat.card_zmultiples, hQ, hn]

theorem comp_ne_zero {X₁ W V : WeierstrassCurve κ} [X₁.IsElliptic] [W.IsElliptic] [V.IsElliptic]
    {χ : Pt X₁ →+ Pt W} (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0)
    {φ : Pt W →+ Pt V} (hφsurj : Function.Surjective φ) : φ.comp χ ≠ 0 := by
  intro h0
  have hsχ : Function.Surjective χ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχ hχ0
  haveI := infinite_point V
  obtain ⟨P, hP⟩ := exists_ne (0 : Pt V)
  obtain ⟨T, rfl⟩ := hφsurj P
  obtain ⟨U, rfl⟩ := hsχ T
  exact hP (DFunLike.congr_fun h0 U)

end Last

end ALDict

open ALDict in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m))
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (hRN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (q : ℕ) [NeZero q] [Fact q.Prime] (hqN : ¬ q ∣ N) (hq'q : ¬ q' ∣ N * q)
    (m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm'₁ : ((m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm'N : ((N * q : ℕ) : ℚ) • ((m'⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm' : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m'))
    (S : Submodule ℤ ℍ[ℚ, a, b]) (hS : S = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m')
    (hSlvl : S.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N * q)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hSn : S = meetOrder R n) (hnorm : Submodule.conjByFiniteIdele S n = S)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : X₁.toAffine.Point →+ W.toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : W.toAffine.Point →+ W'.toAffine.Point)
    (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W') (ψ' : W'.toAffine.Point →+ W.toAffine.Point)
    (hψ' : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
    (hψ'ψ : ψ'.comp ψ = ((N * q : ℕ)) • AddMonoidHom.id _) (hψψ' : ψ.comp ψ' = ((N * q : ℕ)) • AddMonoidHom.id _)
    (hKJ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (hcyc : IsAddCyclic ψ.ker) (hcard : Nat.card ψ.ker = N * q)
    (Q : W.toAffine.Point) (hQC : Q ∈ ψ.ker) (hQ : addOrderOf Q = q)
    (V : WeierstrassCurve κ) [V.IsElliptic] (π : W.toAffine.Point →+ V.toAffine.Point)
    (hπ : π ∈ WeierstrassCurve.rationalHomSet κ W V) (hπker : π.ker = AddSubgroup.zmultiples Q)
    (hπuniv : ∀ (V'' : WeierstrassCurve κ) [V''.IsElliptic] (α : W.toAffine.Point →+ V''.toAffine.Point),
      α ∈ WeierstrassCurve.rationalHomSet κ W V'' → α Q = 0 →
        ∃ γ : V.toAffine.Point →+ V''.toAffine.Point, γ ∈ WeierstrassCurve.rationalHomSet κ V V'' ∧ α = γ.comp π) :
    π.comp χ ≠ 0 ∧
    θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ V (π.comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * n) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ∧
    ∃ (V' : WeierstrassCurve κ) (_ : V'.IsElliptic) (ρ : V.toAffine.Point →+ V'.toAffine.Point)
      (_ : ρ ∈ WeierstrassCurve.rationalHomSet κ V V') (ρ' : V'.toAffine.Point →+ V.toAffine.Point)
      (_ : ρ' ∈ WeierstrassCurve.rationalHomSet κ V' V),
      ρ'.comp ρ = ((N * q : ℕ)) • AddMonoidHom.id _ ∧ ρ.comp ρ' = ((N * q : ℕ)) • AddMonoidHom.id _ ∧
      θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ V' (ρ.comp (π.comp χ)) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * n * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ∧
      ρ.ker = (ψ.ker ⊔ (((q : ℕ)) • AddMonoidHom.id W.toAffine.Point).ker).map π ∧
      IsAddCyclic ρ.ker ∧ Nat.card ρ.ker = N * q := by
  classical
  have hq : q.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNqκ : ((N * q : ℕ) : κ) ≠ 0 := fun h => hq'q ((CharP.cast_eq_zero_iff κ q' (N * q)).mp h)
  have hqκ : ((q : ℕ) : κ) ≠ 0 := fun h =>
    hq'q (dvd_mul_of_dvd_right ((CharP.cast_eq_zero_iff κ q' q).mp h) N)
  have hcop : Nat.Coprime N q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm

  obtain ⟨h1, h2, h3, h4, h5, h6, h9, h7, h8⟩ :=
    QuaternionAlgebra.inv_mul_mem_finiteAdeleBox_and_smul_mul_mem_of_mem_primeHeckeSet_of_conjByFiniteIdele_meetOrder_eq
      q' hdef Λ₁ hΛ₁ N m hm₁ hmN hm R hR hRN q hqN hq'q m' hm'₁ hm'N hm' S hS hSlvl n hn hSn hnorm

  obtain ⟨gE, hgE, hgEord⟩ := exists_zmultiples_eq ψ.ker hcyc (N * q) hcard
  have hgEker : ψ gE = 0 := (AddMonoidHom.mem_ker).mp (hgE ▸ AddSubgroup.mem_zmultiples gE)
  have hQker : ψ Q = 0 := (AddMonoidHom.mem_ker).mp hQC
  have hQord' : addOrderOf (N • gE) = q := by
    rw [addOrderOf_nsmul' gE hN0, hgEord, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hN0)]
  have hQeq : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (N • gE) := by

    have hQmem : Q ∈ AddSubgroup.zmultiples gE := by rw [hgE]; exact hQC
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hQmem
    have hqQ : q • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
    have hdvd : ((N * q : ℕ) : ℤ) ∣ (q : ℤ) * k := by
      rw [← hgEord, addOrderOf_dvd_iff_zsmul_eq_zero, mul_zsmul, hk, natCast_zsmul, hqQ]
    have hNk : (N : ℤ) ∣ k := by
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      have e : ((N * q : ℕ) : ℤ) = (q : ℤ) * (N : ℤ) := by push_cast; ring
      rw [e] at hdvd
      exact (mul_dvd_mul_iff_left hq0).mp hdvd
    obtain ⟨j, rfl⟩ := hNk
    have hle : AddSubgroup.zmultiples Q ≤ AddSubgroup.zmultiples (N • gE) := by
      rw [AddSubgroup.zmultiples_le]
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨j, ?_⟩
      rw [← hk, mul_comm, mul_zsmul, natCast_zsmul]
    haveI : Finite (AddSubgroup.zmultiples (N • gE)) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hQord']; exact hq.ne_zero)
    refine AddSubgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zmultiples, Nat.card_zmultiples, hQ, hQord']
  have hπker' : π.ker = AddSubgroup.zmultiples (N • gE) := hπker.trans hQeq
  have hπuniv' : ∀ (V'' : WeierstrassCurve κ) [V''.IsElliptic] (α : W.toAffine.Point →+ V''.toAffine.Point),
      α ∈ WeierstrassCurve.rationalHomSet κ W V'' → α (N • gE) = 0 →
        ∃ γ : V.toAffine.Point →+ V''.toAffine.Point,
          γ ∈ WeierstrassCurve.rationalHomSet κ V V'' ∧ α = γ.comp π := by
    intro V'' _ α hα h0
    refine hπuniv V'' α hα ?_
    have hQmem : Q ∈ AddSubgroup.zmultiples (N • gE) := hQeq ▸ AddSubgroup.mem_zmultiples Q
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hQmem
    rw [← hk, map_zsmul, h0, smul_zero]

  have hπ0 : π ≠ 0 := by
    intro h0
    haveI : Finite (AddSubgroup.zmultiples Q) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hQ]; exact hq.ne_zero)
    have htop : (AddSubgroup.zmultiples Q : AddSubgroup (Pt W)) = ⊤ := by
      rw [← hπker, h0]; exact AddMonoidHom.ker_zero
    haveI : Finite (Pt W) :=
      Finite.of_surjective (fun s : AddSubgroup.zmultiples Q => (s : Pt W))
        (fun P => ⟨⟨P, by rw [htop]; exact AddSubgroup.mem_top P⟩, rfl⟩)
    haveI := infinite_point W
    exact not_finite (Pt W)
  have hπsurj : Function.Surjective π := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hπ hπ0

  obtain ⟨V₃, hV₃, ψ₃, hψ₃, ψ₃', hψ₃', he1, he2, hcyc₃, hcard₃, hKmem, htors, hkerdesc, hψ₃univ⟩ :=
    level_data W V N q hq hqN hNqκ hqκ ψ.ker gE hgE hgEord π hπ hπker' hπsurj
  haveI := hV₃

  have hK₁ := heart1 q' X₁ hss hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ N q hqN hq'q m' n h1 h2 h3 h4 x W χ hχ hχ0 d hK
    W' ψ hψ ψ' hψ' hψ'ψ hψψ' hKJ gE hgE V π hπ hπker' hπuniv'

  have hK₂' := heart2 X₁ W W' V V₃ θ₁ hθ₁ χ hχ hχ0 ψ hψ ψ' hψ' (N * q) hNqκ hψ'ψ hψψ' gE hgEker Q hQker
    q hqκ π hπ hπsurj hπuniv ψ₃ hψ₃ hKmem htors hkerdesc hψ₃univ
  have hK₂ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ V₃ (ψ₃.comp (π.comp χ)) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * n * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
    rw [hK₂', hK, hKJ]
    exact star_image_inter_eq hΛ₁.1 x n m' N q hq.ne_zero hcop h4 h5 h6 h7 h8 d

  have hker₃ : ψ₃.ker = (ψ.ker ⊔ (((q : ℕ)) • AddMonoidHom.id W.toAffine.Point).ker).map π := by
    have hmemq : ∀ T : Pt W, T ∈ (((q : ℕ)) • AddMonoidHom.id W.toAffine.Point).ker ↔ q • T = 0 := by
      intro T
      rw [AddMonoidHom.mem_ker, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply]
    apply le_antisymm
    · intro v hv
      obtain ⟨P, rfl⟩ := hπsurj v
      obtain ⟨k, T', hT', hP⟩ := hkerdesc P ((AddMonoidHom.mem_ker).mp hv)
      refine AddSubgroup.mem_map.mpr ⟨P, ?_, rfl⟩
      rw [hP]
      refine AddSubgroup.mem_sup.mpr ⟨k • gE, ?_, T', (hmemq T').mpr hT', rfl⟩
      rw [← hgE]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples gE) k
    · intro v hv
      obtain ⟨P, hP, rfl⟩ := AddSubgroup.mem_map.mp hv
      obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hP
      rw [map_add]
      exact add_mem (hKmem y hy) (htors z ((hmemq z).mp hz))
  exact ⟨comp_ne_zero hχ hχ0 hπsurj, hK₁, V₃, hV₃, ψ₃, hψ₃, ψ₃', hψ₃', he1, he2, hK₂, hker₃, hcyc₃, hcard₃⟩

end S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_and_exists_dualPair_ker_eq_map_of_meetOrder_eq_of_conjByFiniteIdele_eq
end P2MW
export P2MW.S_CerednikDrinfeld_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_and_exists_dualPair_ker_eq_map_of_meetOrder_eq_of_conjByFiniteIdele_eq (solution)
