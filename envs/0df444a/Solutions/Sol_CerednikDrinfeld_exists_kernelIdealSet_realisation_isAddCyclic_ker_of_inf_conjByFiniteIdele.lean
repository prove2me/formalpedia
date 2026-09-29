-- Prove2me | solution 1 for CerednikDrinfeld.exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/31bf7458-dfbf-572b-9b6c-d5a99ff9036c

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_quotient_dualPair_kernelIdealSet_comp_eq
import Theorems.Thm_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele
import Theorems.Thm_QuaternionAlgebra_exists_primeHeckeSet_list_prod_mul_eq_of_mem_finiteAdeleBox_of_relIndex_inf_conjByFiniteIdele_eq
import Theorems.Thm_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet
import Theorems.Thm_QuaternionAlgebra_forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_Submodule_finiteAdeleBox_ofFiniteIdele
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange CerednikDrinfeld ModularCurve AlgebraicCurve"

namespace Ws27
namespace C0

theorem natCard_ker_comp {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker := by
  have hmem : ∀ k : ↥(g.comp f).ker, f (k : A) ∈ g.ker := fun k =>
    (AddMonoidHom.mem_ker).mpr ((AddMonoidHom.mem_ker).mp k.2)
  let f' : ↥(g.comp f).ker →+ ↥g.ker := (f.comp (g.comp f).ker.subtype).codRestrict g.ker hmem
  have hsurj : Function.Surjective f' := by
    rintro ⟨c, hc⟩
    obtain ⟨x, rfl⟩ := hf c
    exact ⟨⟨x, (AddMonoidHom.mem_ker).mpr ((AddMonoidHom.mem_ker).mp hc)⟩, Subtype.ext rfl⟩
  have e1 : Nat.card (↥(g.comp f).ker ⧸ f'.ker) = Nat.card g.ker :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f' hsurj).toEquiv
  have e2 : Nat.card f'.ker = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun k => ⟨((k : ↥(g.comp f).ker) : A),
          (AddMonoidHom.mem_ker).mpr (congrArg Subtype.val ((AddMonoidHom.mem_ker).mp k.2))⟩
        invFun := fun y => ⟨⟨(y : A), (AddMonoidHom.mem_ker).mpr (by
            rw [AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).mp y.2, map_zero])⟩,
          (AddMonoidHom.mem_ker).mpr (Subtype.ext ((AddMonoidHom.mem_ker).mp y.2))⟩
        left_inv := fun k => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f'.ker, e1, e2]

end Ws27.C0

namespace Ws3
namespace Chain

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}

def StepDict (X₁ : WeierstrassCurve κ) (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (d : (ℍ[ℚ, a, b])ˣ) (r : ℕ)
    (y s : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Prop :=
  ∀ (W' : WeierstrassCurve κ) [W'.IsElliptic] (χ' : (X₁.baseChange κ).toAffine.Point →+ (W'.baseChange κ).toAffine.Point),
    χ' ∈ WeierstrassCurve.rationalHomSet κ X₁ W' → χ' ≠ 0 →
    θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' χ' =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ y : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) →
    ∃ C : AddSubgroup (W'.baseChange κ).toAffine.Point, (C : Set (W'.baseChange κ).toAffine.Point).Finite ∧ Nat.card C = r ∧
      θ₁ '' {e : ↥(WeierstrassCurve.rationalEndSubring κ X₁) | ∃ σ ∈ WeierstrassCurve.rationalHomSet κ W' X₁,
          (∀ P ∈ C, σ P = 0) ∧ (e : AddMonoid.End (X₁.baseChange κ).toAffine.Point) = σ.comp χ'} =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (y * s) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])

theorem comp_nsmul_id_comp {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : B →+ C) (g : A →+ B) (n : ℕ) : f.comp ((n • AddMonoidHom.id B).comp g) = n • f.comp g := by
  ext x
  simp [map_nsmul]

theorem exists_chain_realisation
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : (X₁.baseChange κ).toAffine.Point, q' • P = 0 → P = 0)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]) (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (d : (ℍ[ℚ, a, b])ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : (X₁.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0)
    (xs ss : ℕ → (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (rs : ℕ → ℕ)
    (hχK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (xs 0) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (k : ℕ) (hxs : ∀ i < k, xs (i + 1) = xs i * ss i)
    (hstep : ∀ i < k, StepDict X₁ θ₁ Λ₁ d (rs i) (xs i) (ss i)) :
    ∃ (W' : WeierstrassCurve κ) (_ : W'.IsElliptic) (ψ : (W.baseChange κ).toAffine.Point →+ (W'.baseChange κ).toAffine.Point)
      (_ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W')
      (ψ' : (W'.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point) (_ : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W),
      ψ.comp χ ≠ 0 ∧
      θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (xs k) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ∧
      ψ'.comp ψ = (∏ i ∈ Finset.range k, rs i) • AddMonoidHom.id _ ∧
      ψ.comp ψ' = (∏ i ∈ Finset.range k, rs i) • AddMonoidHom.id _ ∧
      Nat.card ψ.ker = ∏ i ∈ Finset.range k, rs i := by
  induction k with
  | zero =>
    refine ⟨W, inferInstance, AddMonoidHom.id _, WeierstrassCurve.id_mem_rationalHomSet κ W, AddMonoidHom.id _,
      WeierstrassCurve.id_mem_rationalHomSet κ W, ?_, ?_, ?_, ?_, ?_⟩
    · rw [AddMonoidHom.id_comp]; exact hχ0
    · rw [AddMonoidHom.id_comp]; exact hχK
    · simp
    · simp
    · rw [Finset.prod_range_zero]
      have : (AddMonoidHom.id (W.baseChange κ).toAffine.Point).ker = ⊥ := by
        ext P; simp [AddMonoidHom.mem_ker]
      rw [this, AddSubgroup.card_bot]
  | succ j ih =>
    obtain ⟨Wj, hWj, ψ, hψ, ψ', hψ', hne, hK, hd1, hd2, hkc⟩ :=
      ih (fun i hi => hxs i (Nat.lt_succ_of_lt hi)) (fun i hi => hstep i (Nat.lt_succ_of_lt hi))

    have hχj : ψ.comp χ ∈ WeierstrassCurve.rationalHomSet κ X₁ Wj := WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W Wj hχ hψ
    obtain ⟨C, hC, hcard, hAnn⟩ := hstep j (Nat.lt_succ_self j) Wj (ψ.comp χ) hχj hne hK
    have hssWj : ∀ P : (Wj.baseChange κ).toAffine.Point, q' • P = 0 → P = 0 :=
      WeierstrassCurve.forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero q' X₁ hss Wj (ψ.comp χ) hχj hne

    obtain ⟨V, hV, φ, hφ, φ', hφ', hker, -, hφd1, hφd2, hSet⟩ :=
      WeierstrassCurve.exists_quotient_dualPair_kernelIdealSet_comp_eq q' X₁ Wj hssWj (ψ.comp χ) C hC
    haveI := hV
    have hφne : φ ≠ 0 := by
      intro h0
      haveI : Finite C := hC
      obtain ⟨r, hrge, hrp⟩ := Nat.exists_infinite_primes (max (Nat.card C) q' + 1)
      have hrq : r ≠ q' := by omega
      have hrκ : (r : κ) ≠ 0 := by
        intro h
        exact hrq ((Nat.prime_dvd_prime_iff_eq Fact.out hrp).mp ((CharP.cast_eq_zero_iff κ q' r).mp h)).symm
      obtain ⟨R, hR⟩ : ∃ R : (Wj.baseChange κ).toAffine.Point, addOrderOf R = r :=
        WeierstrassCurve.exists_addOrderOf_eq_prime_of_isAlgClosed Wj r hrp hrκ
      have hRC : R ∈ C := by rw [← hker, h0, AddMonoidHom.ker_zero]; trivial
      have hdvd : addOrderOf (⟨R, hRC⟩ : C) ∣ Nat.card C := addOrderOf_dvd_natCard _
      rw [AddSubgroup.addOrderOf_mk, hR] at hdvd
      have := Nat.le_of_dvd Nat.card_pos hdvd
      omega
    have hsurjj : Function.Surjective (ψ.comp χ) := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hχj hne
    have hψ0 : ψ ≠ 0 := by
      intro h0; apply hne; rw [h0, AddMonoidHom.zero_comp]
    have hψsurj : Function.Surjective ψ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hψ hψ0
    refine ⟨V, hV, φ.comp ψ, WeierstrassCurve.comp_mem_rationalHomSet κ W Wj V hψ hφ, ψ'.comp φ',
      WeierstrassCurve.comp_mem_rationalHomSet κ V Wj W hφ' hψ', ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro h0
      apply hφne
      rw [← AddMonoidHom.cancel_right hsurjj, AddMonoidHom.zero_comp]
      exact h0
    ·
      rw [hxs j (Nat.lt_succ_self j), ← hAnn]
      show θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ V (φ.comp (ψ.comp χ)) = _
      rw [hSet]
    ·
      calc (ψ'.comp φ').comp (φ.comp ψ) = ψ'.comp ((φ'.comp φ).comp ψ) := rfl
        _ = Nat.card C • ψ'.comp ψ := by rw [hφd1, comp_nsmul_id_comp]
        _ = (∏ i ∈ Finset.range (j + 1), rs i) • AddMonoidHom.id _ := by
          rw [hd1, hcard, smul_smul, Finset.prod_range_succ, mul_comm]
    · calc (φ.comp ψ).comp (ψ'.comp φ') = φ.comp ((ψ.comp ψ').comp φ') := rfl
        _ = (∏ i ∈ Finset.range j, rs i) • φ.comp φ' := by rw [hd2, comp_nsmul_id_comp]
        _ = (∏ i ∈ Finset.range (j + 1), rs i) • AddMonoidHom.id _ := by
          rw [hφd2, hcard, smul_smul, Finset.prod_range_succ]
    ·
      rw [Ws27.C0.natCard_ker_comp ψ φ hψsurj, hker, hcard, hkc, Finset.prod_range_succ, mul_comm]

end Ws3.Chain

namespace Ws3
namespace Prim

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {a b : ℚ}

theorem not_forall_smul_eq_zero_mem_ker_of_not_le_smul
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic]
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]) (d : (ℍ[ℚ, a, b])ˣ)
    (I J : Submodule ℤ ℍ[ℚ, a, b])
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : (X₁.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W)
    (hχK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ = star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : (W.baseChange κ).toAffine.Point →+ (W'.baseChange κ).toAffine.Point)
    (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W')
    (hψK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) = star '' ((d • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (p : ℕ) (hp : (p : κ) ≠ 0) (hnot : ¬ J ≤ (p : ℤ) • I) :
    ¬ (∀ P : (W.baseChange κ).toAffine.Point, (p : ℤ) • P = 0 → P ∈ ψ.ker) := by
  intro hall
  apply hnot

  obtain ⟨g, hg, hψg⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W W' hp hψ
    (fun P hP => (AddMonoidHom.mem_ker).mp (hall P hP))
  intro j hj

  have hw : star ((d : ℍ[ℚ, a, b]) * j) ∈ θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) := by
    rw [hψK]
    refine ⟨(d : ℍ[ℚ, a, b]) * j, ?_, rfl⟩
    rw [SetLike.mem_coe, Units.smul_def, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨j, hj, by simp [smul_eq_mul]⟩
  obtain ⟨e, ⟨ρ, hρ, he⟩, hθe⟩ := hw

  have hρg : ρ.comp g ∈ WeierstrassCurve.rationalHomSet κ W X₁ := WeierstrassCurve.comp_mem_rationalHomSet κ W W' X₁ hg hρ
  have hmem : ((ρ.comp g).comp χ : AddMonoid.End (X₁.baseChange κ).toAffine.Point) ∈ WeierstrassCurve.rationalEndSubring κ X₁ :=
    Subring.subset_closure (WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W X₁ hχ hρg)
  have he'K : (⟨_, hmem⟩ : ↥(WeierstrassCurve.rationalEndSubring κ X₁)) ∈ WeierstrassCurve.kernelIdealSet κ X₁ W χ := ⟨ρ.comp g, hρg, rfl⟩
  have hee' : e = (p : ↥(WeierstrassCurve.rationalEndSubring κ X₁)) * ⟨_, hmem⟩ := by
    apply Subtype.ext
    rw [he, Subring.coe_mul, Subring.coe_natCast]
    apply DFunLike.ext
    intro Q
    show ρ (ψ (χ Q)) = _
    rw [AddMonoid.End.coe_mul, Function.comp_apply, AddMonoid.End.natCast_apply, hψg, map_zsmul, natCast_zsmul]
    rfl

  have hθe' : θ₁ ⟨_, hmem⟩ ∈ star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
    rw [← hχK]; exact ⟨_, he'K, rfl⟩
  obtain ⟨v, hv, hsv⟩ := hθe'
  rw [SetLike.mem_coe, Units.smul_def, Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨i, hi, rfl⟩ := hv

  have h1 : star ((d : ℍ[ℚ, a, b]) * j) = (p : ℍ[ℚ, a, b]) * star ((d : ℍ[ℚ, a, b]) • i) := by
    rw [← hθe, hee', map_mul, map_natCast, hsv]
  have h2 : (d : ℍ[ℚ, a, b]) * j = (d : ℍ[ℚ, a, b]) * (i * (p : ℍ[ℚ, a, b])) := by
    have := congrArg star h1
    rw [star_star, star_mul, star_star, star_natCast, smul_eq_mul, mul_assoc] at this
    exact this
  have h3 : j = i * (p : ℍ[ℚ, a, b]) := (Units.mul_right_inj d).mp h2
  have h4 : j = (p : ℤ) • i := by
    rw [h3, zsmul_eq_mul, Int.cast_natCast, (Nat.cast_commute p i).eq]
  rw [h4]
  exact Submodule.smul_mem_pointwise_smul i (p : ℤ) I hi

end Ws3.Prim

namespace Ws27
namespace C0

variable {a b : ℚ}

section Box

open IsDedekindDomain

set_option hygiene false in
local notation "𝔸f" => ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ

theorem tmul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ)
    {c : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hc : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) :
    (1 : 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_finiteAdeleBox hΛ.one_mem fun v => one_mem _

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {u v : 𝔸f} (hu : u ∈ Submodule.finiteAdeleBox Λ) (hv : v ∈ Submodule.finiteAdeleBox Λ) :
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
      exact mul_neg (α := 𝔸f) _ _
  | zero => rw [zero_mul]; exact zero_mem _
  | add u u' _ _ ihu ihu' => rw [add_mul]; exact add_mem ihu ihu'
  | neg u _ ihu =>
    convert neg_mem ihu using 1
    exact neg_mul (α := 𝔸f) _ _

theorem mem_ofFiniteIdele_iff' (R : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔸f)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele R g ↔
      ((g⁻¹ : (𝔸f)ˣ) : 𝔸f) * (z ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox R := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨t, ht, h⟩
    have h' : (g : 𝔸f) * t = z ⊗ₜ[ℚ] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) := h
    rw [← h', Units.inv_mul_cancel_left]
    exact ht
  · intro h
    exact ⟨_, h, by simp⟩

theorem ofFiniteIdele_le_of_inv_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {g g' : (𝔸f)ˣ} (h : ((g'⁻¹ * g : (𝔸f)ˣ) : 𝔸f) ∈ Submodule.finiteAdeleBox Λ) :
    Submodule.ofFiniteIdele Λ g ≤ Submodule.ofFiniteIdele Λ g' := by
  intro z hz
  rw [mem_ofFiniteIdele_iff'] at hz ⊢
  have := mul_mem_finiteAdeleBox hΛ h hz
  rwa [Units.val_mul, mul_assoc, Units.mul_inv_cancel_left] at this

theorem finiteAdeleBox_mono {S R : Submodule ℤ ℍ[ℚ, a, b]} (h : S ≤ R) :
    Submodule.finiteAdeleBox S ≤ Submodule.finiteAdeleBox R := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem inv_mul_mem_finiteAdeleBox_of_le {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {g g' : (𝔸f)ˣ} (hle : Submodule.ofFiniteIdele Λ g ≤ Submodule.ofFiniteIdele Λ g') :
    ((g'⁻¹ * g : (𝔸f)ˣ) : 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
  have hbox := finiteAdeleBox_mono hle
  rw [Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop g,
    Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop g'] at hbox
  have h1 : (g : 𝔸f) * 1 ∈ (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g' : 𝔸f)) :=
    hbox ⟨1, one_mem_finiteAdeleBox hΛ, rfl⟩
  obtain ⟨w, hw, hgw⟩ := h1
  have : ((g'⁻¹ * g : (𝔸f)ˣ) : 𝔸f) = w := by
    rw [Units.val_mul, ← mul_one (g : 𝔸f), ← hgw]
    show _ * (g' * w) = w
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [this]; exact hw

noncomputable def ratIdele (s : ℚ) (hs : s ≠ 0) : (𝔸f)ˣ :=
  Units.map (algebraMap ℚ (𝔸f)).toMonoidHom (Units.mk0 s hs)

theorem val_ratIdele (s : ℚ) (hs : s ≠ 0) : ((ratIdele (a := a) (b := b) s hs : (𝔸f)ˣ) : 𝔸f) = algebraMap ℚ (𝔸f) s := rfl

theorem val_ratIdele_inv (s : ℚ) (hs : s ≠ 0) :
    (((ratIdele (a := a) (b := b) s hs)⁻¹ : (𝔸f)ˣ) : 𝔸f) = algebraMap ℚ (𝔸f) s⁻¹ := by
  rw [ratIdele, ← map_inv, Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]
  rfl

theorem mem_ofFiniteIdele_mul_ratIdele_iff (R : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔸f)ˣ) (s : ℚ) (hs : s ≠ 0)
    (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele R (g * ratIdele s hs) ↔ s⁻¹ • z ∈ Submodule.ofFiniteIdele R g := by
  rw [mem_ofFiniteIdele_iff', mem_ofFiniteIdele_iff', mul_inv_rev, Units.val_mul, val_ratIdele_inv,
    ← Algebra.smul_def, smul_mul_assoc, ← mul_smul_comm, TensorProduct.smul_tmul']

theorem smul_inv_mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {g g' : (𝔸f)ˣ} {s : ℕ} (hs : s ≠ 0)
    (h : ∀ z ∈ Submodule.ofFiniteIdele Λ g, (s : ℤ) • z ∈ Submodule.ofFiniteIdele Λ g') :
    ((s : ℕ) : ℚ) • ((g'⁻¹ * g : (𝔸f)ˣ) : 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
  have hsQ : ((s : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hs
  have hle : Submodule.ofFiniteIdele Λ (g * ratIdele (s : ℚ) hsQ) ≤ Submodule.ofFiniteIdele Λ g' := by
    intro z hz
    rw [mem_ofFiniteIdele_mul_ratIdele_iff] at hz
    have := h _ hz
    rwa [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, smul_smul, mul_inv_cancel₀ hsQ, one_smul] at this
  have hmem := inv_mul_mem_finiteAdeleBox_of_le hΛ hle
  rwa [← mul_assoc, Units.val_mul, val_ratIdele, ← Algebra.commutes, ← Algebra.smul_def] at hmem

theorem mem_finiteAdeleBox_of_coprime {Λ : Submodule ℤ ℍ[ℚ, a, b]} {A : 𝔸f} {M c : ℕ}
    (hcop : Nat.Coprime M c)
    (hM : ((M : ℕ) : ℚ) • A ∈ Submodule.finiteAdeleBox Λ) (hc : ((c : ℕ) : ℚ) • A ∈ Submodule.finiteAdeleBox Λ) :
    A ∈ Submodule.finiteAdeleBox Λ := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : A = (u : ℚ) • (((M : ℕ) : ℚ) • A) + (v : ℚ) • (((c : ℕ) : ℚ) • A) := by
    rw [smul_smul, smul_smul, ← add_smul]
    have : (u : ℚ) * (M : ℚ) + (v : ℚ) * (c : ℚ) = 1 := by exact_mod_cast huv
    rw [this, one_smul]
  rw [e, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact add_mem (AddSubgroup.zsmul_mem _ hM u) (AddSubgroup.zsmul_mem _ hc v)

end Box

section NotLe

open IsDedekindDomain

set_option hygiene false in
local notation "𝔸f" => ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ

theorem not_le_smul_of_inv_smul_not_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x g : (𝔸f)ˣ) {p : ℕ} (hp : p.Prime)
    (hprim : ((p : ℚ)⁻¹ • ((g : (𝔸f)ˣ) : 𝔸f)) ∉ Submodule.finiteAdeleBox Λ) :
    ¬ Submodule.ofFiniteIdele Λ (x * g) ≤ (p : ℤ) • Submodule.ofFiniteIdele Λ x := by
  intro hle
  apply hprim
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hle' : Submodule.ofFiniteIdele Λ (x * g) ≤ Submodule.ofFiniteIdele Λ (x * ratIdele (p : ℚ) hpQ) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hle hz)
    rw [mem_ofFiniteIdele_mul_ratIdele_iff, ← Int.cast_smul_eq_zsmul ℚ (p : ℤ) i, smul_smul, Int.cast_natCast,
      inv_mul_cancel₀ hpQ, one_smul]
    exact hi
  have hmem := inv_mul_mem_finiteAdeleBox_of_le hΛ hle'
  have e : (x * ratIdele (p : ℚ) hpQ)⁻¹ * (x * g) = (ratIdele (a := a) (b := b) (p : ℚ) hpQ)⁻¹ * g := by group
  rwa [e, Units.val_mul, val_ratIdele_inv, ← Algebra.smul_def] at hmem

end NotLe

theorem isAddCyclic_of_card_torsion_prime_le {G : Type*} [AddCommGroup G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → Nat.card {g : G // p • g = 0} ≤ p) : IsAddCyclic G := by
  classical
  haveI := Fintype.ofFinite G
  refine isAddCyclic_of_card_nsmul_eq_zero_le fun n => ?_
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨c, hc⟩ := Nat.minFac_dvd n
      set p := n.minFac with hpdef
      have hp2 : 2 ≤ p := hp.two_le
      have hc0 : 0 < c := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hc; omega)
      have hcn : c < n := by
        rw [hc]
        calc c = 1 * c := (one_mul c).symm
          _ < p * c := Nat.mul_lt_mul_of_pos_right (by omega) hc0
      have hfib : ∀ y ∈ (Finset.univ.filter fun g : G => n • g = 0).image (fun g => p • g),
          ((Finset.univ.filter fun g : G => n • g = 0).filter (fun g => p • g = y)).card ≤ p := by
        intro y hy
        obtain ⟨g₀, -, rfl⟩ := Finset.mem_image.mp hy
        calc ((Finset.univ.filter fun g : G => n • g = 0).filter (fun g => p • g = p • g₀)).card
            ≤ (Finset.univ.filter fun g : G => p • g = 0).card := by
              refine Finset.card_le_card_of_injOn (fun g => g - g₀) ?_ ?_
              · intro g hg
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
                rw [smul_sub, hg.2, sub_self]
              · intro g _ g' _ hgg'
                exact sub_left_injective hgg'
          _ = Nat.card {g : G // p • g = 0} := by
              rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          _ ≤ p := h p hp
      have himg : (Finset.univ.filter fun g : G => n • g = 0).image (fun g => p • g) ⊆
          Finset.univ.filter fun g : G => c • g = 0 := by
        intro y hy
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
        rw [smul_smul, mul_comm, ← hc]
        exact hg
      calc (Finset.univ.filter fun g : G => n • g = 0).card
          ≤ p * ((Finset.univ.filter fun g : G => n • g = 0).image (fun g => p • g)).card :=
            Finset.card_le_mul_card_image _ p hfib
        _ ≤ p * (Finset.univ.filter fun g : G => c • g = 0).card :=
            Nat.mul_le_mul_left p (Finset.card_le_card himg)
        _ ≤ p * c := Nat.mul_le_mul_left p (ih c hcn hc0)
        _ = n := hc.symm
    · have hn1 : n = 1 := by omega
      subst hn1
      calc (Finset.univ.filter fun g : G => 1 • g = 0).card ≤ ({0} : Finset G).card := by
            refine Finset.card_le_card ?_
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, one_smul] at hg
            simp [hg]
        _ = 1 := Finset.card_singleton 0

theorem card_torsion_ker_le_of_not_contains_torsion
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    {W W' : WeierstrassCurve κ} [W.IsElliptic] [W'.IsElliptic]
    (ψ : (W.baseChange κ).toAffine.Point →+ (W'.baseChange κ).toAffine.Point)
    (hW0 : ∀ P : (W.baseChange κ).toAffine.Point, q' • P = 0 → P = 0)
    (hnot : ∀ p : ℕ, p.Prime → (p : κ) ≠ 0 →
      ¬ ∀ P : (W.baseChange κ).toAffine.Point, (p : ℤ) • P = 0 → P ∈ ψ.ker) :
    ∀ p : ℕ, p.Prime → Nat.card {g : ↥ψ.ker // p • g = 0} ≤ p := by
  intro p hp
  by_cases hpκ : (p : κ) = 0
  ·
    have hpq : p = q' := ((Nat.prime_dvd_prime_iff_eq Fact.out hp).mp ((CharP.cast_eq_zero_iff κ q' p).mp hpκ)).symm
    have hone : Nat.card {g : ↥ψ.ker // p • g = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun g g' => Subtype.ext (Subtype.ext ?_)⟩, ⟨⟨0, smul_zero _⟩⟩⟩
      have h1 : ((g : ↥ψ.ker) : (W.baseChange κ).toAffine.Point) = 0 := hW0 _ (by
        rw [← hpq]; exact_mod_cast congrArg (fun t : ↥ψ.ker => (t : (W.baseChange κ).toAffine.Point)) g.2)
      have h2 : ((g' : ↥ψ.ker) : (W.baseChange κ).toAffine.Point) = 0 := hW0 _ (by
        rw [← hpq]; exact_mod_cast congrArg (fun t : ↥ψ.ker => (t : (W.baseChange κ).toAffine.Point)) g'.2)
      rw [h1, h2]
    rw [hone]; exact hp.one_lt.le
  ·
    obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (F := κ) (K := κ) W (n := p) hpκ
    set T : AddSubgroup (W.baseChange κ).toAffine.Point :=
      (Submodule.torsionBy ℤ (W.baseChange κ).toAffine.Point (p : ℤ)).toAddSubgroup with hTdef
    have hTmem : ∀ P : (W.baseChange κ).toAffine.Point, P ∈ T ↔ (p : ℤ) • P = 0 := fun P =>
      Submodule.mem_torsionBy_iff _ _
    have hcardT : Nat.card ↥T = p ^ 2 := by
      have : Nat.card ↥(Submodule.torsionBy ℤ (W.baseChange κ).toAffine.Point (p : ℤ)) = p ^ 2 := by
        rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
      exact this
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Finite ↥T := Nat.finite_of_card_ne_zero (by rw [hcardT]; exact pow_ne_zero 2 hp.ne_zero)

    set H : AddSubgroup ↥T := ψ.ker.addSubgroupOf T with hHdef
    have hHcard : Nat.card ↥H = Nat.card {g : ↥ψ.ker // p • g = 0} := by
      refine Nat.card_congr
        { toFun := fun t => ⟨⟨((t : ↥T) : (W.baseChange κ).toAffine.Point), AddSubgroup.mem_addSubgroupOf.mp t.2⟩,
            Subtype.ext ?_⟩
          invFun := fun g => ⟨⟨((g : ↥ψ.ker) : (W.baseChange κ).toAffine.Point), ?_⟩, ?_⟩
          left_inv := fun t => Subtype.ext (Subtype.ext rfl)
          right_inv := fun g => Subtype.ext (Subtype.ext rfl) }
      · have ht := (hTmem _).mp (t : ↥T).2
        rw [natCast_zsmul] at ht
        exact ht
      · rw [hTmem, natCast_zsmul]
        exact congrArg (fun s : ↥ψ.ker => (s : (W.baseChange κ).toAffine.Point)) g.2
      · exact AddSubgroup.mem_addSubgroupOf.mpr (g : ↥ψ.ker).2
    rw [← hHcard]
    have hdvd : Nat.card ↥H ∣ p ^ 2 := hcardT ▸ AddSubgroup.card_addSubgroup_dvd_card H
    obtain ⟨i, hi, hHi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [hHi]
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · interval_cases i
      · rw [pow_zero]; exact hp.one_lt.le
      · rw [pow_one]
    · exfalso
      have hi2' : i = 2 := le_antisymm hi hi2
      rw [hi2'] at hHi
      have htop : H = ⊤ := AddSubgroup.eq_top_of_card_eq H (by rw [hHi, hcardT])
      apply hnot p hp hpκ
      intro P hP
      have hPT : P ∈ T := (hTmem P).mpr hP
      have : (⟨P, hPT⟩ : ↥T) ∈ H := by rw [htop]; exact AddSubgroup.mem_top _
      exact AddSubgroup.mem_addSubgroupOf.mp this

end Ws27.C0

namespace Ws27
namespace C0

open IsDedekindDomain

set_option hygiene false in
local notation "𝔸f" => ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ

theorem main
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (m : (𝔸f)ˣ)
    (hm₁ : ((m : (𝔸f)ˣ) : 𝔸f) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (𝔸f)ˣ) : 𝔸f) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (x : (𝔸f)ˣ) :
    ∃ (W : WeierstrassCurve κ) (_ : W.IsElliptic) (χ : X₁.toAffine.Point →+ W.toAffine.Point)
      (_ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (_ : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
      (_ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
      (W' : WeierstrassCurve κ) (_ : W'.IsElliptic) (ψ : W.toAffine.Point →+ W'.toAffine.Point)
      (_ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W')
      (ψ' : W'.toAffine.Point →+ W.toAffine.Point) (_ : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
      (_ : ψ'.comp ψ = (N : ℕ) • AddMonoidHom.id _) (_ : ψ.comp ψ' = (N : ℕ) • AddMonoidHom.id _)
      (_ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])),
      IsAddCyclic ψ.ker ∧ Nat.card ψ.ker = N := by
  have hΛ : IsOrder Λ₁ := hΛ₁.isOrder

  obtain ⟨W, hW, χ, hχ, hχ0, d, hK⟩ :=
    CerednikDrinfeld.exists_kernelIdealSet_eq_star_smul_ofFiniteIdele q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ x
  haveI := hW

  obtain ⟨k, rs, ss, hsteps, hprod, v, hv, hmfac⟩ :=
    QuaternionAlgebra.exists_primeHeckeSet_list_prod_mul_eq_of_mem_finiteAdeleBox_of_relIndex_inf_conjByFiniteIdele_eq
      Λ₁ hΛ₁ N m hm₁ hmN hRN

  let xs : ℕ → (𝔸f)ˣ := fun i => x * ((List.range i).map ss).prod
  have hxs : ∀ i < k, xs (i + 1) = xs i * ss i := by
    intro i _
    show x * ((List.range (i + 1)).map ss).prod = x * ((List.range i).map ss).prod * ss i
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc]
  have hxs0 : xs 0 = x := by
    show x * ((List.range 0).map ss).prod = x
    rw [List.range_zero, List.map_nil, List.prod_nil, mul_one]
  have hrq : ∀ i < k, rs i ≠ q' := by
    intro i hi h
    apply hq'N
    rw [← h, ← hprod]
    exact Finset.dvd_prod_of_mem rs (Finset.mem_range.mpr hi)
  have hstep : ∀ i < k, Ws3.Chain.StepDict X₁ θ₁ Λ₁ d (rs i) (xs i) (ss i) := fun i hi =>
    CerednikDrinfeld.forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet
      q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ d (rs i) (hsteps i hi).1 (hrq i hi) (xs i) (ss i) (hsteps i hi).2

  obtain ⟨W', hW', ψ, hψ, ψ', hψ', -, hKψ, hd1, hd2, hcard⟩ :=
    Ws3.Chain.exists_chain_realisation q' X₁ hss θ₁ Λ₁ d W χ hχ hχ0 xs ss rs (by rw [hxs0]; exact hK) k hxs hstep
  haveI := hW'
  rw [hprod] at hd1 hd2 hcard

  have hofeq : Submodule.ofFiniteIdele Λ₁ (xs k) = Submodule.ofFiniteIdele Λ₁ (x * m) := by
    rw [Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ₁ hΛ.fg hΛ.spanTop]
    have : (xs k)⁻¹ * (x * m) = v := by
      rw [hmfac]
      show (x * ((List.range k).map ss).prod)⁻¹ * (x * (((List.range k).map ss).prod * v)) = v
      group
    rw [this]
    exact hv
  rw [hofeq] at hKψ

  have hprim := QuaternionAlgebra.forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq
    Λ₁ hΛ₁ N m hm₁ hmN hRN
  have hW0 : ∀ P : (W.baseChange κ).toAffine.Point, q' • P = 0 → P = 0 :=
    WeierstrassCurve.forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero q' X₁ hss W χ hχ hχ0
  have hnot : ∀ p : ℕ, p.Prime → (p : κ) ≠ 0 →
      ¬ ∀ P : (W.baseChange κ).toAffine.Point, (p : ℤ) • P = 0 → P ∈ ψ.ker := fun p hp hpκ =>
    Ws3.Prim.not_forall_smul_eq_zero_mem_ker_of_not_le_smul X₁ θ₁ d (Submodule.ofFiniteIdele Λ₁ x)
      (Submodule.ofFiniteIdele Λ₁ (x * m)) W χ hχ hK W' ψ hψ hKψ p hpκ
      (not_le_smul_of_inv_smul_not_mem hΛ x m hp (hprim p hp))
  haveI : Finite ↥ψ.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; exact NeZero.ne N)
  have hcyc : IsAddCyclic ψ.ker :=
    isAddCyclic_of_card_torsion_prime_le (card_torsion_ker_le_of_not_contains_torsion q' ψ hW0 hnot)
  exact ⟨W, hW, χ, hχ, hχ0, d, hK, W', hW', ψ, hψ, ψ', hψ', hd1, hd2, hKψ, hcyc, hcard⟩

end Ws27.C0

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
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ (W : WeierstrassCurve κ) (_ : W.IsElliptic) (χ : X₁.toAffine.Point →+ W.toAffine.Point)
      (_ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (_ : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
      (_ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
      (W' : WeierstrassCurve κ) (_ : W'.IsElliptic) (ψ : W.toAffine.Point →+ W'.toAffine.Point)
      (_ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W')
      (ψ' : W'.toAffine.Point →+ W.toAffine.Point) (_ : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
      (_ : ψ'.comp ψ = (N : ℕ) • AddMonoidHom.id _) (_ : ψ.comp ψ' = (N : ℕ) • AddMonoidHom.id _)
      (_ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * m) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])),
      IsAddCyclic ψ.ker ∧ Nat.card ψ.ker = N := by
  subst hR
  exact Ws27.C0.main q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ N hq'N m hm₁ hmN hRN x

end S_CerednikDrinfeld_exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele
end P2MW
export P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_realisation_isAddCyclic_ker_of_inf_conjByFiniteIdele (solution)
