-- Prove2me | solution 1 for CerednikDrinfeld.natCard_isUnitOf_conjByFiniteIdele_eq_natCard_rationalAut_map_ker_eq_of_image_kernelIdealSet_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6b7f5a87-6ba7-581e-8ff1-3cfd8478661a

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_CerednikDrinfeld_exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Theorems.Thm_Submodule_mem_conjByFiniteIdele_diagonal_mul_iff
import Theorems.Thm_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_neg_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_mem_rationalEndSubring_iff_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_natCard_isUnitOf_conjByFiniteIdele_eq_natCard_rationalAut_map_ker_eq_of_image_kernelIdealSet_comp_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq FrobeniusEndo.linePencil_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange IsDedekindDomain"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq"
namespace UnitsRationalAut
p2m_open "CerednikDrinfeld"

section Points

p2m_open "Polynomial WeierstrassCurve~card"

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

theorem infinite_point (W : WeierstrassCurve F) [IsAlgClosed k] [W.IsElliptic] : Infinite (Pt k W) := by
  haveI : (W.baseChange k).IsElliptic :=
    (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  have hy : ∀ x : k, ∃ y : k, (W.baseChange k).toAffine.Nonsingular x y := by
    intro x
    have hdeg : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
      rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
        WeierstrassCurve.Affine.degree_polynomial]
      norm_num
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, ((W.baseChange k).toAffine.equation_iff_nonsingular).mp ?_⟩
    rw [IsRoot.def, map_evalRingHom_eval] at hy
    exact hy
  choose f hf using hy
  refine Infinite.of_injective (fun x : k => (Affine.Point.some x (f x) (hf x) : Pt k W)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

variable [DecidableEq k]
variable {W₁ W₂ : WeierstrassCurve F}

theorem sub_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂)
    (hβ : β ∈ rationalHomSet k W₁ W₂) : α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact add_mem_rationalHomSet k W₁ W₂ hα (neg_mem_rationalHomSet k W₁ W₂ hβ)

theorem eq_zero_of_finite_range [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (hfin : (Set.range α).Finite) :
    α = 0 := by
  by_contra hα0
  have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k hα hα0
  haveI := infinite_point (k := k) W₂
  rw [hsurj.range_eq] at hfin
  exact Set.infinite_univ hfin

theorem finite_torsion [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : n ≠ 0)
    (hnk : (n : k) ≠ 0) : {P : Pt k W | (n : ℤ) • P = 0}.Finite := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (Pt k W) (n : ℤ)) = n ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hnk
  haveI : Finite (Submodule.torsionBy ℤ (Pt k W) (n : ℤ)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]; exact pow_ne_zero 2 hn
  have : {P : Pt k W | (n : ℤ) • P = 0} = ((Submodule.torsionBy ℤ (Pt k W) (n : ℤ)) : Set (Pt k W)) := by
    ext P; exact (Submodule.mem_torsionBy_iff _ _).symm
  rw [this]
  exact Set.toFinite _

theorem eq_zero_of_nsmul_eq_zero [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) {n : ℕ} (hn : n ≠ 0)
    (hnk : (n : k) ≠ 0) (h : n • α = 0) : α = 0 := by
  refine eq_zero_of_finite_range hα ((finite_torsion W₂ hn hnk).subset ?_)
  rintro _ ⟨P, rfl⟩
  have := DFunLike.congr_fun h P
  rw [AddMonoidHom.nsmul_apply, AddMonoidHom.zero_apply] at this
  change (n : ℤ) • α P = 0
  rw [natCast_zsmul]; exact this

theorem eq_zero_of_comp_eq_zero [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic] {W₃ : WeierstrassCurve F}
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0)
    {ρ : Pt k W₂ →+ Pt k W₃} (h : ρ.comp α = 0) : ρ = 0 := by
  ext Q
  obtain ⟨P, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hα hα0 Q
  exact DFunLike.congr_fun h P

end Points

section Factor

p2m_open "WeierstrassCurve~card"

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {V W W' : WeierstrassCurve κ} [V.IsElliptic] [W.IsElliptic] [W'.IsElliptic]

theorem forall_ker_iff_exists_comp {N : ℕ} (hN : (N : κ) ≠ 0)
    {ψ : Pt κ W →+ Pt κ W'} (hψ : ψ ∈ rationalHomSet κ W W') {ψ' : Pt κ W' →+ Pt κ W}
    (hψ' : ψ' ∈ rationalHomSet κ W' W)
    (h1 : ψ'.comp ψ = (N : ℕ) • AddMonoidHom.id _) (h2 : ψ.comp ψ' = (N : ℕ) • AddMonoidHom.id _)
    {σ : Pt κ W →+ Pt κ V} (hσ : σ ∈ rationalHomSet κ W V) :
    (∀ T ∈ ψ.ker, σ T = 0) ↔ ∃ ρ' ∈ rationalHomSet κ W' V, σ = ρ'.comp ψ := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  constructor
  · intro hker
    have hkill : ∀ Q : Pt κ W', (N : ℤ) • Q = 0 → (σ.comp ψ') Q = 0 := by
      intro Q hQ
      apply hker
      rw [AddMonoidHom.mem_ker, show ψ (ψ' Q) = (ψ.comp ψ') Q from rfl, h2, AddMonoidHom.nsmul_apply,
        AddMonoidHom.id_apply, ← natCast_zsmul, hQ]
    obtain ⟨β, hβ, hβeq⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W' V hN
      (comp_mem_rationalHomSet κ W' W V hψ' hσ) hkill
    refine ⟨β, hβ, ?_⟩
    have hD : σ - β.comp ψ ∈ rationalHomSet κ W V :=
      sub_mem_rationalHomSet hσ (comp_mem_rationalHomSet κ W W' V hψ hβ)
    have hND : N • (σ - β.comp ψ) = 0 := by
      ext P
      rw [AddMonoidHom.nsmul_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, smul_sub, ← natCast_zsmul,
        ← natCast_zsmul, ← hβeq (ψ P), AddMonoidHom.comp_apply, show ψ' (ψ P) = (ψ'.comp ψ) P from rfl, h1,
        AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, map_nsmul, natCast_zsmul, AddMonoidHom.zero_apply, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_nsmul_eq_zero hD hN0 hN hND)
  · rintro ⟨ρ', hρ', rfl⟩ T hT
    rw [AddMonoidHom.comp_apply, show ψ T = 0 from hT, map_zero]

end Factor

section Quaternion

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem nrd_ne_zero (ha : a < 0) (hb : b < 0) {z : ℍ[ℚ, a, b]} (hz : z ≠ 0) : nrd z ≠ 0 := by
  intro h0
  apply hz
  have h1 : 0 ≤ z.re ^ 2 := sq_nonneg _
  have h2 : 0 ≤ -a * z.imI ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ -b * z.imJ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : 0 ≤ a * b * z.imK ^ 2 := mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (sq_nonneg _)
  have hn : nrd z = z.re ^ 2 + -a * z.imI ^ 2 + -b * z.imJ ^ 2 + a * b * z.imK ^ 2 := by
    rw [nrd]; ring
  rw [hn] at h0
  have e1 : z.re ^ 2 = 0 := by linarith
  have e2 : -a * z.imI ^ 2 = 0 := by linarith
  have e3 : -b * z.imJ ^ 2 = 0 := by linarith
  have e4 : a * b * z.imK ^ 2 = 0 := by linarith
  have hab : a * b ≠ 0 := (mul_pos_of_neg_of_neg ha hb).ne'
  ext
  · simpa using e1
  · simpa [ha.ne] using e2
  · simpa [hb.ne] using e3
  · simpa [hab] using e4

def invQ (z : ℍ[ℚ, a, b]) : ℍ[ℚ, a, b] := (nrd z)⁻¹ • star z

theorem invQ_mul (ha : a < 0) (hb : b < 0) {z : ℍ[ℚ, a, b]} (hz : z ≠ 0) : invQ z * z = 1 := by
  rw [invQ, smul_mul_assoc, star_mul_eq_coe_nrd, smul_coe, inv_mul_cancel₀ (nrd_ne_zero ha hb hz)]
  rfl

theorem mul_left_cancel_of_ne_zero (ha : a < 0) (hb : b < 0) {z u w : ℍ[ℚ, a, b]} (hz : z ≠ 0)
    (h : z * u = z * w) : u = w := by
  have := congrArg (invQ z * ·) h
  simpa only [← mul_assoc, invQ_mul ha hb hz, one_mul] using this

theorem mem_ofFiniteIdele_iff' (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele Λ g ↔
      ∃ w ∈ Submodule.finiteAdeleBox Λ, (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * w = z ⊗ₜ[ℚ] (1 : 𝔸f) := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  rfl

theorem exists_natCast_mem_ofFiniteIdele {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ∃ n : ℕ, n ≠ 0 ∧ (n : ℍ[ℚ, a, b]) ∈ Submodule.ofFiniteIdele Λ g := by
  obtain ⟨n, hn, hmem⟩ := Submodule.exists_ne_zero_natCast_smul_mem_finiteAdeleBox Λ hΛ.spanTop
    ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
  refine ⟨n, hn, ?_⟩
  rw [mem_ofFiniteIdele_iff']
  refine ⟨_, hmem, ?_⟩
  rw [mul_smul_comm, Units.mul_inv, show (n : ℍ[ℚ, a, b]) = ((n : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b]) by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one], ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

theorem natCast_ne_zero_quat {n : ℕ} (hn : n ≠ 0) : (n : ℍ[ℚ, a, b]) ≠ 0 := by
  intro h0
  apply hn
  have := congrArg QuaternionAlgebra.re h0
  simpa using this

theorem exists_ne_zero_mem_star_image {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (d : (ℍ[ℚ, a, b])ˣ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    ∃ w ∈ star '' ((d • Submodule.ofFiniteIdele Λ g : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]), w ≠ 0 := by
  obtain ⟨n, hn, hmem⟩ := exists_natCast_mem_ofFiniteIdele hΛ g
  refine ⟨star ((d : ℍ[ℚ, a, b]) * n), ⟨(d : ℍ[ℚ, a, b]) * n, ?_, rfl⟩, ?_⟩
  · exact Submodule.smul_mem_pointwise_smul _ _ _ hmem
  · rw [ne_eq, star_eq_zero]
    intro h
    have : ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((d : ℍ[ℚ, a, b]) * n) = 0 := by rw [h, mul_zero]
    rw [← mul_assoc, Units.inv_mul, one_mul] at this
    exact natCast_ne_zero_quat hn this

def conjMap (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) →+ (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :=
  (AddMonoidHom.mulRight ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)).comp
    (AddMonoidHom.mulLeft (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f))

theorem conjMap_apply (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (w : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    conjMap g w = (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * w * ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := rfl

theorem conjMap_injective (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : Function.Injective (conjMap g) := by
  intro u w h
  rw [conjMap_apply, conjMap_apply] at h
  have := (Units.mul_left_inj g⁻¹).mp h
  exact (Units.mul_right_inj g).mp this

theorem conjMap_comp (g m : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : (conjMap g).comp (conjMap m) = conjMap (g * m) := by
  ext w
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, conjMap_apply, Units.val_mul, mul_inv_rev, mul_assoc]

theorem mem_conjByFiniteIdele_iff' (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔ z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ (Submodule.finiteAdeleBox Λ).map (conjMap g) :=
  Submodule.mem_conjByFiniteIdele_iff Λ g z

theorem mem_conjByFiniteIdele_inf_iff {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : IsOrder Λ₁) (m : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    {S : Submodule ℤ ℍ[ℚ, a, b]} (hS : S = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m) (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele S g ↔
      z ∈ Submodule.conjByFiniteIdele Λ₁ g ∧ z ∈ Submodule.conjByFiniteIdele Λ₁ (g * m) := by
  obtain ⟨hbox, -, -, -⟩ :=
    QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le Λ₁ hΛ₁ m
  rw [mem_conjByFiniteIdele_iff', mem_conjByFiniteIdele_iff', mem_conjByFiniteIdele_iff', hS, hbox,
    AddSubgroup.map_inf_eq _ _ _ (conjMap_injective g), AddSubgroup.mem_inf]
  refine and_congr_right fun _ => ?_
  change _ ∈ ((Submodule.finiteAdeleBox Λ₁).map (conjMap m)).map (conjMap g) ↔ _
  rw [AddSubgroup.map_map, conjMap_comp]

def cj (d : (ℍ[ℚ, a, b])ˣ) (z : ℍ[ℚ, a, b]) : ℍ[ℚ, a, b] :=
  ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * (d : ℍ[ℚ, a, b])

theorem cj_mul (d : (ℍ[ℚ, a, b])ˣ) (z w : ℍ[ℚ, a, b]) : cj d (z * w) = cj d z * cj d w := by
  simp only [cj, mul_assoc, Units.mul_inv_cancel_left]

theorem cj_one (d : (ℍ[ℚ, a, b])ˣ) : cj d 1 = 1 := by
  simp only [cj, mul_one, Units.inv_mul]

theorem cj_injective (d : (ℍ[ℚ, a, b])ˣ) : Function.Injective (cj d) := by
  intro z w h
  have := congrArg (fun u => (d : ℍ[ℚ, a, b]) * u * ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) h
  simpa only [cj, mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one] using this

theorem cj_conj (d : (ℍ[ℚ, a, b])ˣ) (u : ℍ[ℚ, a, b]) :
    cj d ((d : ℍ[ℚ, a, b]) * u * ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = u := by
  simp only [cj, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]

theorem mem_conj_diag_iff (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (d : (ℍ[ℚ, a, b])ˣ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ₁ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * g) ↔
      cj d z ∈ Submodule.conjByFiniteIdele Λ₁ g :=
  Submodule.mem_conjByFiniteIdele_diagonal_mul_iff Λ₁ d g z

end Quaternion

section Frame

p2m_open "WeierstrassCurve~card"

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}
variable {X₁ W W' : WeierstrassCurve κ} [X₁.IsElliptic] [W.IsElliptic] [W'.IsElliptic]

abbrev toHom {V : WeierstrassCurve κ} (α : ↥(rationalEndSubring κ V)) : Pt κ V →+ Pt κ V :=
  ((α : AddMonoid.End (Pt κ V)) : Pt κ V →+ Pt κ V)

theorem toHom_mem {V : WeierstrassCurve κ} [V.IsElliptic] (α : ↥(rationalEndSubring κ V)) :
    toHom α ∈ rationalHomSet κ V V :=
  (WeierstrassCurve.mem_rationalEndSubring_iff_mem_rationalHomSet κ V _).mp α.2

def toEnd {V : WeierstrassCurve κ} (ι : Pt κ V →+ Pt κ V) (hι : ι ∈ rationalHomSet κ V V) :
    ↥(rationalEndSubring κ V) :=
  ⟨(ι : AddMonoid.End (Pt κ V)), Subring.subset_closure hι⟩

theorem toHom_toEnd {V : WeierstrassCurve κ} (ι : Pt κ V →+ Pt κ V) (hι : ι ∈ rationalHomSet κ V V) :
    toHom (toEnd ι hι) = ι := rfl

theorem toEnd_toHom {V : WeierstrassCurve κ} [V.IsElliptic] (α : ↥(rationalEndSubring κ V)) :
    toEnd (toHom α) (toHom_mem α) = α := Subtype.ext rfl

structure Frame (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (θ₁ : ↥(rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]) (N : ℕ)
    (m x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (S : Submodule ℤ ℍ[ℚ, a, b])
    (χ : Pt κ X₁ →+ Pt κ W) (d : (ℍ[ℚ, a, b])ˣ)
    (ψ : Pt κ W →+ Pt κ W') (ψ' : Pt κ W' →+ Pt κ W)
    (θW : ↥(rationalEndSubring κ W) →+* ℍ[ℚ, a, b]) (θW' : ↥(rationalEndSubring κ W') →+* ℍ[ℚ, a, b]) : Prop where
  neg_a : a < 0
  neg_b : b < 0
  isOrder : IsOrder Λ₁
  inj : Function.Injective θ₁
  hN : (N : κ) ≠ 0
  hS : S = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m
  mem : χ ∈ rationalHomSet κ X₁ W
  ne_zero : χ ≠ 0
  memψ : ψ ∈ rationalHomSet κ W W'
  memψ' : ψ' ∈ rationalHomSet κ W' W
  dual₁ : ψ'.comp ψ = (N : ℕ) • AddMonoidHom.id _
  dual₂ : ψ.comp ψ' = (N : ℕ) • AddMonoidHom.id _
  hK' : θ₁ '' kernelIdealSet κ X₁ W' (ψ.comp χ) =
    star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])
  injW : Function.Injective θW
  rangeW : Set.range θW =
    (Submodule.conjByFiniteIdele Λ₁ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x) : Set ℍ[ℚ, a, b])
  lawW : ∀ ρ ∈ rationalHomSet κ W X₁, ∀ (α : ↥(rationalEndSubring κ W)) (e e' : ↥(rationalEndSubring κ X₁)),
    (e : AddMonoid.End (Pt κ X₁)) = ρ.comp χ →
    (e' : AddMonoid.End (Pt κ X₁)) = (ρ.comp (toHom α)).comp χ → θ₁ e' = θ₁ e * θW α
  injW' : Function.Injective θW'
  rangeW' : Set.range θW' =
    (Submodule.conjByFiniteIdele Λ₁ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * (x * m)) : Set ℍ[ℚ, a, b])
  lawW' : ∀ ρ' ∈ rationalHomSet κ W' X₁, ∀ (α : ↥(rationalEndSubring κ W')) (e e' : ↥(rationalEndSubring κ X₁)),
    (e : AddMonoid.End (Pt κ X₁)) = ρ'.comp (ψ.comp χ) →
    (e' : AddMonoid.End (Pt κ X₁)) = (ρ'.comp (toHom α)).comp (ψ.comp χ) → θ₁ e' = θ₁ e * θW' α

variable {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} {θ₁ : ↥(rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]} {N : ℕ}
  {m x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} {S : Submodule ℤ ℍ[ℚ, a, b]}
  {χ : Pt κ X₁ →+ Pt κ W} {d : (ℍ[ℚ, a, b])ˣ} {ψ : Pt κ W →+ Pt κ W'} {ψ' : Pt κ W' →+ Pt κ W}
  {θW : ↥(rationalEndSubring κ W) →+* ℍ[ℚ, a, b]} {θW' : ↥(rationalEndSubring κ W') →+* ℍ[ℚ, a, b]}

theorem Frame.comp_mem (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') : ψ.comp χ ∈ rationalHomSet κ X₁ W' :=
  comp_mem_rationalHomSet κ X₁ W W' hF.mem hF.memψ

theorem Frame.exists_rho (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') :
    ∃ ρ'₀ ∈ rationalHomSet κ W' X₁, ρ'₀ ≠ 0 ∧ ψ.comp χ ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_mem_star_image hF.isOrder d (x * m)
  rw [← hF.hK'] at hw
  obtain ⟨e, ⟨ρ', hρ', he⟩, rfl⟩ := hw
  have he0 : (e : AddMonoid.End (Pt κ X₁)) ≠ 0 := by
    intro h0
    apply hw0
    have : e = 0 := Subtype.ext h0
    rw [this, map_zero]
  refine ⟨ρ', hρ', ?_, ?_⟩
  · rintro rfl
    apply he0
    rw [he, AddMonoidHom.zero_comp]
    rfl
  · intro h0
    apply he0
    rw [he, h0, AddMonoidHom.comp_zero]
    rfl

def Frame.rho (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') : Pt κ W' →+ Pt κ X₁ := hF.exists_rho.choose

theorem Frame.rho_mem (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') : hF.rho ∈ rationalHomSet κ W' X₁ :=
  hF.exists_rho.choose_spec.1

theorem Frame.rho_ne_zero (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') : hF.rho ≠ 0 :=
  hF.exists_rho.choose_spec.2.1

theorem Frame.comp_ne_zero (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') : ψ.comp χ ≠ 0 :=
  hF.exists_rho.choose_spec.2.2

theorem Frame.theta_rho_ne_zero (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') (e : ↥(rationalEndSubring κ X₁))
    (he : (e : AddMonoid.End (Pt κ X₁)) = hF.rho.comp (ψ.comp χ)) : θ₁ e ≠ 0 := by
  intro h0
  have h1 : e = 0 := hF.inj (by rw [h0, map_zero])
  have h2 : hF.rho.comp (ψ.comp χ) = 0 := by rw [← he, h1]; rfl
  exact hF.rho_ne_zero (eq_zero_of_comp_eq_zero hF.comp_mem hF.comp_ne_zero h2)

theorem Frame.mem_end (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') {σ : Pt κ W →+ Pt κ X₁}
    (hσ : σ ∈ rationalHomSet κ W X₁) :
    ((σ.comp χ : Pt κ X₁ →+ Pt κ X₁) : AddMonoid.End (Pt κ X₁)) ∈ rationalEndSubring κ X₁ :=
  Subring.subset_closure (comp_mem_rationalHomSet κ X₁ W X₁ hF.mem hσ)

theorem Frame.mem_range_of_stab (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') (α : ↥(rationalEndSubring κ W))
    (hα : ∀ P ∈ ψ.ker, toHom α P ∈ ψ.ker) : θW α ∈ Set.range θW' := by

  have hσ : ψ.comp (toHom α) ∈ rationalHomSet κ W W' := comp_mem_rationalHomSet κ W W W' (toHom_mem α) hF.memψ
  have hkill : ∀ T ∈ ψ.ker, (ψ.comp (toHom α)) T = 0 := fun T hT => hα T hT
  obtain ⟨α'', hα'', hfac⟩ :=
    (forall_ker_iff_exists_comp (V := W') hF.hN hF.memψ hF.memψ' hF.dual₁ hF.dual₂ hσ).mp hkill
  set α₂ : ↥(rationalEndSubring κ W') := ⟨α'', Subring.subset_closure hα''⟩ with hα₂

  have hρ : hF.rho.comp ψ ∈ rationalHomSet κ W X₁ := comp_mem_rationalHomSet κ W W' X₁ hF.memψ hF.rho_mem
  have hρα : (hF.rho.comp ψ).comp (toHom α) ∈ rationalHomSet κ W X₁ :=
    comp_mem_rationalHomSet κ W W X₁ (toHom_mem α) hρ
  set e : ↥(rationalEndSubring κ X₁) := ⟨(hF.rho.comp ψ).comp χ, hF.mem_end hρ⟩ with he
  set e' : ↥(rationalEndSubring κ X₁) := ⟨((hF.rho.comp ψ).comp (toHom α)).comp χ, hF.mem_end hρα⟩ with he'
  have l1 : θ₁ e' = θ₁ e * θW α := hF.lawW _ hρ α e e' rfl rfl
  have l2 : θ₁ e' = θ₁ e * θW' α₂ := by
    refine hF.lawW' _ hF.rho_mem α₂ e e' rfl ?_
    change ((hF.rho.comp ψ).comp (toHom α)).comp χ = (hF.rho.comp (toHom α₂)).comp (ψ.comp χ)
    have hα₂' : toHom α₂ = α'' := rfl
    ext P
    have := DFunLike.congr_fun hfac (χ P)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, hα₂', this]
  have hne : θ₁ e ≠ 0 := hF.theta_rho_ne_zero e rfl
  exact ⟨α₂, (mul_left_cancel_of_ne_zero hF.neg_a hF.neg_b hne (l2.symm.trans l1)).symm ▸ rfl⟩

theorem Frame.stab_of_mem_range (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') (α : ↥(rationalEndSubring κ W))
    (hα : θW α ∈ Set.range θW') : ∀ P ∈ ψ.ker, toHom α P ∈ ψ.ker := by
  obtain ⟨α₂, hα₂⟩ := hα

  set δ : Pt κ W →+ Pt κ W' := ψ.comp (toHom α) - (toHom α₂).comp ψ with hδ
  have hδmem : δ ∈ rationalHomSet κ W W' :=
    sub_mem_rationalHomSet (comp_mem_rationalHomSet κ W W W' (toHom_mem α) hF.memψ)
      (comp_mem_rationalHomSet κ W W' W' hF.memψ (toHom_mem α₂))
  have hδ0 : δ = 0 := by
    by_contra hne
    apply hF.rho_ne_zero
    refine eq_zero_of_comp_eq_zero hδmem hne ?_

    have hρ : hF.rho.comp ψ ∈ rationalHomSet κ W X₁ := comp_mem_rationalHomSet κ W W' X₁ hF.memψ hF.rho_mem
    have hρα : (hF.rho.comp ψ).comp (toHom α) ∈ rationalHomSet κ W X₁ :=
      comp_mem_rationalHomSet κ W W X₁ (toHom_mem α) hρ
    have hρα₂ : (hF.rho.comp (toHom α₂)).comp ψ ∈ rationalHomSet κ W X₁ :=
      comp_mem_rationalHomSet κ W W' X₁ hF.memψ (comp_mem_rationalHomSet κ W' W' X₁ (toHom_mem α₂) hF.rho_mem)
    set e : ↥(rationalEndSubring κ X₁) := ⟨(hF.rho.comp ψ).comp χ, hF.mem_end hρ⟩ with he
    set e₁ : ↥(rationalEndSubring κ X₁) := ⟨((hF.rho.comp ψ).comp (toHom α)).comp χ, hF.mem_end hρα⟩ with he₁
    set e₂ : ↥(rationalEndSubring κ X₁) := ⟨((hF.rho.comp (toHom α₂)).comp ψ).comp χ, hF.mem_end hρα₂⟩ with he₂
    have l1 : θ₁ e₁ = θ₁ e * θW α := hF.lawW _ hρ α e e₁ rfl rfl
    have l2 : θ₁ e₂ = θ₁ e * θW' α₂ := hF.lawW' _ hF.rho_mem α₂ e e₂ rfl rfl
    have h12 : e₁ = e₂ := hF.inj (by rw [l1, l2, hα₂])
    have h12' := congrArg (fun z : ↥(rationalEndSubring κ X₁) => ((z : AddMonoid.End (Pt κ X₁)) : Pt κ X₁ →+ Pt κ X₁)) h12
    simp only [he₁, he₂] at h12'
    ext Q
    obtain ⟨P, rfl⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hF.mem hF.ne_zero Q
    have key : hF.rho (ψ (toHom α (χ P))) = hF.rho (toHom α₂ (ψ (χ P))) := DFunLike.congr_fun h12' P
    rw [AddMonoidHom.zero_apply, AddMonoidHom.comp_apply, hδ, AddMonoidHom.sub_apply, map_sub, sub_eq_zero]
    exact key
  intro P hP
  have := DFunLike.congr_fun hδ0 P
  simp only [hδ, AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zero_apply,
    sub_eq_zero] at this
  rw [AddMonoidHom.mem_ker, this, show ψ P = 0 from hP, map_zero]

abbrev RatAut (ψ : Pt κ W →+ Pt κ W') : Type :=
  {ι : Pt κ W →+ Pt κ W //
    ι ∈ rationalHomSet κ W W ∧
    (∃ ι' ∈ rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
    (ψ.ker).map ι = ψ.ker}

abbrev OrderUnits (S : Submodule ℤ ℍ[ℚ, a, b]) (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Type :=
  {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele S x) u}

theorem Frame.cj_mem (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') (α : ↥(rationalEndSubring κ W))
    (hα : ∀ P ∈ ψ.ker, toHom α P ∈ ψ.ker) : cj d (θW α) ∈ Submodule.conjByFiniteIdele S x := by
  rw [mem_conjByFiniteIdele_inf_iff hF.isOrder m hF.hS x]
  constructor
  · rw [← mem_conj_diag_iff]
    have : θW α ∈ Set.range θW := ⟨α, rfl⟩
    rw [hF.rangeW] at this
    exact this
  · rw [← mem_conj_diag_iff]
    have := hF.mem_range_of_stab α hα
    rw [hF.rangeW'] at this
    exact this

theorem stab_of_map_eq {ι : Pt κ W →+ Pt κ W} (h : (ψ.ker).map ι = ψ.ker) :
    ∀ P ∈ ψ.ker, ι P ∈ ψ.ker := by
  intro P hP
  rw [← h]
  exact AddSubgroup.mem_map_of_mem ι hP

theorem stab_inv_of_map_eq {ι ι' : Pt κ W →+ Pt κ W} (h : (ψ.ker).map ι = ψ.ker)
    (h₁ : ι'.comp ι = AddMonoidHom.id _) : ∀ P ∈ ψ.ker, ι' P ∈ ψ.ker := by
  intro P hP
  rw [← h] at hP
  obtain ⟨Q, hQ, rfl⟩ := AddSubgroup.mem_map.mp hP
  rw [show ι' (ι Q) = (ι'.comp ι) Q from rfl, h₁, AddMonoidHom.id_apply]
  exact hQ

theorem toEnd_mul_toEnd {V : WeierstrassCurve κ} (ι ι' : Pt κ V →+ Pt κ V) (hι : ι ∈ rationalHomSet κ V V)
    (hι' : ι' ∈ rationalHomSet κ V V) (h : ι.comp ι' = AddMonoidHom.id _) :
    toEnd ι hι * toEnd ι' hι' = 1 :=
  Subtype.ext h

def Frame.G (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') (ι : RatAut (W := W) ψ) : OrderUnits S x :=
  ⟨cj d (θW (toEnd ι.1 ι.2.1)), by
    obtain ⟨hι, ⟨ι', hι', h₁, h₂⟩, hmap⟩ := ι.2
    refine ⟨hF.cj_mem _ (stab_of_map_eq hmap), cj d (θW (toEnd ι' hι')),
      hF.cj_mem _ (stab_inv_of_map_eq hmap h₁), ?_, ?_⟩
    · rw [← cj_mul, ← map_mul, toEnd_mul_toEnd _ _ _ _ h₂, map_one, cj_one]
    · rw [← cj_mul, ← map_mul, toEnd_mul_toEnd _ _ _ _ h₁, map_one, cj_one]⟩

theorem Frame.G_val (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') (ι : RatAut (W := W) ψ) :
    (hF.G ι : ℍ[ℚ, a, b]) = cj d (θW (toEnd ι.1 ι.2.1)) := rfl

theorem Frame.G_injective (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') : Function.Injective hF.G := by
  intro ι₁ ι₂ h
  have h1 := congrArg Subtype.val h
  rw [hF.G_val, hF.G_val] at h1
  have h2 : toEnd ι₁.1 ι₁.2.1 = toEnd ι₂.1 ι₂.2.1 := hF.injW (cj_injective d h1)
  have h3 := congrArg toHom h2
  rw [toHom_toEnd, toHom_toEnd] at h3
  exact Subtype.ext h3

theorem Frame.G_surjective (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') : Function.Surjective hF.G := by
  rintro ⟨u, hu, v, hv, huv, hvu⟩
  have hu2 := (mem_conjByFiniteIdele_inf_iff hF.isOrder m hF.hS x u).mp hu
  have hv2 := (mem_conjByFiniteIdele_inf_iff hF.isOrder m hF.hS x v).mp hv

  have hu' : (d : ℍ[ℚ, a, b]) * u * ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Set.range θW := by
    rw [hF.rangeW, SetLike.mem_coe, mem_conj_diag_iff, cj_conj]
    exact hu2.1
  have hv' : (d : ℍ[ℚ, a, b]) * v * ((d⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Set.range θW := by
    rw [hF.rangeW, SetLike.mem_coe, mem_conj_diag_iff, cj_conj]
    exact hv2.1
  obtain ⟨α₀, hα₀⟩ := hu'
  obtain ⟨β₀, hβ₀⟩ := hv'
  have hαβ : α₀ * β₀ = 1 := hF.injW (by
    rw [map_mul, hα₀, hβ₀, map_one]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc u, huv, one_mul, Units.mul_inv])
  have hβα : β₀ * α₀ = 1 := hF.injW (by
    rw [map_mul, hα₀, hβ₀, map_one]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc v, hvu, one_mul, Units.mul_inv])

  have hstabα : ∀ P ∈ ψ.ker, toHom α₀ P ∈ ψ.ker := by
    refine hF.stab_of_mem_range α₀ ?_
    rw [hF.rangeW', SetLike.mem_coe, mem_conj_diag_iff, hα₀, cj_conj]
    exact hu2.2
  have hstabβ : ∀ P ∈ ψ.ker, toHom β₀ P ∈ ψ.ker := by
    refine hF.stab_of_mem_range β₀ ?_
    rw [hF.rangeW', SetLike.mem_coe, mem_conj_diag_iff, hβ₀, cj_conj]
    exact hv2.2

  have hcomp₁ : (toHom β₀).comp (toHom α₀) = AddMonoidHom.id _ := by
    have := congrArg (fun z : ↥(rationalEndSubring κ W) => toHom z) hβα
    exact this
  have hcomp₂ : (toHom α₀).comp (toHom β₀) = AddMonoidHom.id _ := by
    have := congrArg (fun z : ↥(rationalEndSubring κ W) => toHom z) hαβ
    exact this
  have hmap : (ψ.ker).map (toHom α₀) = ψ.ker := by
    apply le_antisymm
    · rintro _ ⟨P, hP, rfl⟩
      exact hstabα P hP
    · intro P hP
      refine AddSubgroup.mem_map.mpr ⟨toHom β₀ P, hstabβ P hP, ?_⟩
      change ((toHom α₀).comp (toHom β₀)) P = P
      rw [hcomp₂, AddMonoidHom.id_apply]
  refine ⟨⟨toHom α₀, toHom_mem α₀, ⟨toHom β₀, toHom_mem β₀, hcomp₁, hcomp₂⟩, hmap⟩, Subtype.ext ?_⟩
  rw [hF.G_val]
  change cj d (θW (toEnd (toHom α₀) (toHom_mem α₀))) = u
  rw [toEnd_toHom, hα₀, cj_conj]

theorem Frame.natCard_eq (hF : Frame Λ₁ θ₁ N m x S χ d ψ ψ' θW θW') :
    Nat.card (OrderUnits S x) = Nat.card (RatAut (W := W) ψ) :=
  (Nat.card_congr (Equiv.ofBijective hF.G ⟨hF.G_injective, hF.G_surjective⟩)).symm

end Frame

end CerednikDrinfeld.UnitsRationalAut

end

p2m_open "WeierstrassCurve~card" in open CerednikDrinfeld.UnitsRationalAut  in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (M' : ℕ) [NeZero M'] (hq'M' : ¬ q' ∣ M')
    (m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm'₁ : ((m' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm'N : ((M' : ℕ) : ℚ) • ((m'⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm' : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m'))
    (S : Submodule ℤ ℍ[ℚ, a, b]) (hS : S = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m')
    (hSlvl : S.toAddSubgroup.relIndex Λ₁.toAddSubgroup = M')
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : X₁.toAffine.Point →+ W.toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : W.toAffine.Point →+ W'.toAffine.Point)
    (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W') (ψ' : W'.toAffine.Point →+ W.toAffine.Point)
    (hψ' : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
    (hψd : ψ'.comp ψ = (M' : ℕ) • AddMonoidHom.id _ ∧ ψ.comp ψ' = (M' : ℕ) • AddMonoidHom.id _)
    (hKJ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m') : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    :
    Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele S x) u} =
      Nat.card {ι : W.toAffine.Point →+ W.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ W W ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        (ψ.ker).map ι = ψ.ker} := by

  have hN : (M' : κ) ≠ 0 := by
    intro h0
    exact hq'M' ((CharP.cast_eq_zero_iff κ q' M').mp h0)

  have hψχ : ψ.comp χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W' := comp_mem_rationalHomSet κ X₁ W W' hχ hψ
  have hψχ0 : ψ.comp χ ≠ 0 := by
    obtain ⟨w, hw, hw0⟩ := exists_ne_zero_mem_star_image hΛ₁.isOrder d (x * m')
    rw [← hKJ] at hw
    obtain ⟨e, ⟨ρ', hρ', he⟩, rfl⟩ := hw
    intro h0
    apply hw0
    have : e = 0 := Subtype.ext (by
      rw [he]
      ext P
      change ρ' (ψ (χ P)) = 0
      have h1 : ψ (χ P) = 0 := DFunLike.congr_fun h0 P
      rw [h1]
      exact ρ'.map_zero)
    rw [this, map_zero]

  obtain ⟨θW, hinjW, hrangeW, hlawW⟩ :=
    CerednikDrinfeld.exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq
      q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ x W χ hχ hχ0 d hK
  obtain ⟨θW', hinjW', hrangeW', hlawW'⟩ :=
    CerednikDrinfeld.exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq
      q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ (x * m') W' (ψ.comp χ) hψχ hψχ0 d hKJ
  have hF : Frame (X₁ := X₁) (W := W) (W' := W') Λ₁ θ₁ M' m' x S χ d ψ ψ' θW θW' :=
    ⟨hdef.neg_left, hdef.neg_right, hΛ₁.isOrder, hθ₁, hN, hS, hχ, hχ0, hψ, hψ', hψd.1, hψd.2, hKJ, hinjW, hrangeW,
      hlawW, hinjW', hrangeW', hlawW'⟩
  exact hF.natCard_eq

end S_CerednikDrinfeld_natCard_isUnitOf_conjByFiniteIdele_eq_natCard_rationalAut_map_ker_eq_of_image_kernelIdealSet_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_natCard_isUnitOf_conjByFiniteIdele_eq_natCard_rationalAut_map_ker_eq_of_image_kernelIdealSet_comp_eq (solution)
