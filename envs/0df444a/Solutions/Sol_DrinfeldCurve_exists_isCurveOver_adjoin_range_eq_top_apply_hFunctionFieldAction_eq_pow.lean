-- Prove2me | solution 1 for DrinfeldCurve.exists_isCurveOver_adjoin_range_eq_top_apply_hFunctionFieldAction_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b1d7ebdd-5159-5a91-b6fc-e2957c39730d

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_DrinfeldCurve_isDomain_coordRing_of_ne_one
import Theorems.Thm_DrinfeldCurve_isCurveOver_drinfeldFunctionField
import Theorems.Thm_AlgebraicCurve_exists_isCurveOver_adjoin_range_eq_top_apply_algEquiv_eq_pow_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_exists_isCurveOver_adjoin_range_eq_top_apply_hFunctionFieldAction_eq_pow
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

namespace MvPolynomial
p2m_export "MvPolynomial" "X map aeval_X ext algebraMap_apply ringHom_ext comap algebraMap_eq algHom_C map_C C algebraTensorAlgEquiv map_X aeval_C algHom_ext induction_on aeval"
namespace BaseChangeFF
p2m_open "MvPolynomial"

open TensorProduct

variable (k₀ K : Type*) [Field k₀] [Field K] [Algebra k₀ K] (σ : Type*)

@[reducible] noncomputable def coeffAlgebra : Algebra (MvPolynomial σ k₀) (MvPolynomial σ K) :=
  (MvPolynomial.map (algebraMap k₀ K)).toAlgebra

attribute [local instance] coeffAlgebra

theorem smul_def' (p : MvPolynomial σ k₀) (g : MvPolynomial σ K) :
    p • g = MvPolynomial.map (algebraMap k₀ K) p * g := rfl

noncomputable def e₀ : (MvPolynomial σ k₀) ⊗[k₀] K ≃ₗ[k₀] MvPolynomial σ K :=
  (TensorProduct.comm k₀ (MvPolynomial σ k₀) K).trans
    ((MvPolynomial.algebraTensorAlgEquiv (σ := σ) k₀ K).toLinearEquiv.restrictScalars k₀)

theorem e₀_tmul (p : MvPolynomial σ k₀) (c : K) :
    e₀ k₀ K σ (p ⊗ₜ c) = c • MvPolynomial.map (algebraMap k₀ K) p := by
  simp [e₀]

noncomputable def baseChangeEquiv :
    (MvPolynomial σ k₀) ⊗[k₀] K ≃ₗ[MvPolynomial σ k₀] MvPolynomial σ K :=
  { e₀ k₀ K σ with
    map_smul' := by
      intro p t
      change e₀ k₀ K σ (p • t) = p • e₀ k₀ K σ t
      induction t using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul a c =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, e₀_tmul, e₀_tmul, map_mul, smul_def', mul_smul_comm]
      | add t₁ t₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add] }

theorem faithfullyFlat : Module.FaithfullyFlat (MvPolynomial σ k₀) (MvPolynomial σ K) :=
  Module.FaithfullyFlat.of_linearEquiv _ _ (baseChangeEquiv k₀ K σ).symm

end MvPolynomial.BaseChangeFF

namespace MvPolynomial
p2m_export "MvPolynomial" "X map aeval_X ext algebraMap_apply ringHom_ext comap algebraMap_eq algHom_C map_C C algebraTensorAlgEquiv map_X aeval_C algHom_ext induction_on aeval"
namespace BaseChangeFF
p2m_open "MvPolynomial"

theorem comap_map_eq {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K] {σ : Type*}
    (I : Ideal (MvPolynomial σ k₀)) :
    (I.map (MvPolynomial.map (algebraMap k₀ K))).comap (MvPolynomial.map (algebraMap k₀ K)) = I := by
  letI := MvPolynomial.BaseChangeFF.coeffAlgebra k₀ K σ
  haveI := MvPolynomial.BaseChangeFF.faithfullyFlat k₀ K σ
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

end MvPolynomial.BaseChangeFF

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_algebraMap drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective algHom_ext x y scalePoly_X ofZMod ofZMod_pow_card substPoly_X scalarOf hSubgroup hAction_mk isDomain_coordRing_of_ne_one isCurveOver_drinfeldFunctionField"
namespace AJAssembly
p2m_open "DrinfeldCurve"

p2m_open "MvPolynomial P2MW.S_DrinfeldCurve_exists_isCurveOver_adjoin_range_eq_top_apply_hFunctionFieldAction_eq_pow.MvPolynomial"

section CoordRing

variable (q : ℕ) (k₀ K : Type) [Field k₀] [Field K] [Algebra k₀ K]

theorem map_drinfeldPoly : MvPolynomial.map (algebraMap k₀ K) (drinfeldPoly q k₀) = drinfeldPoly q K := by
  simp [drinfeldPoly, map_sub, map_mul, map_pow, map_X]

theorem map_drinfeldIdeal :
    (drinfeldIdeal q k₀).map (MvPolynomial.map (algebraMap k₀ K)) = drinfeldIdeal q K := by
  rw [drinfeldIdeal, drinfeldIdeal, Ideal.map_span, Set.image_singleton, map_sub, map_one, map_drinfeldPoly]

noncomputable def ι₀ : CoordRing q k₀ →+* CoordRing q K :=
  Ideal.Quotient.lift (drinfeldIdeal q k₀)
    ((Ideal.Quotient.mk (drinfeldIdeal q K)).comp (MvPolynomial.map (algebraMap k₀ K)))
    (fun a ha => by
      change Ideal.Quotient.mk (drinfeldIdeal q K) (MvPolynomial.map (algebraMap k₀ K) a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, ← map_drinfeldIdeal q k₀ K]
      exact Ideal.mem_map_of_mem _ ha)

theorem ι₀_mk (g : MvPolynomial (Fin 2) k₀) :
    ι₀ q k₀ K (mk q k₀ g) = mk q K (MvPolynomial.map (algebraMap k₀ K) g) := rfl

theorem ι₀_x : ι₀ q k₀ K (x q k₀) = x q K := by
  rw [x, ι₀_mk, map_X]; rfl

theorem ι₀_y : ι₀ q k₀ K (y q k₀) = y q K := by
  rw [y, ι₀_mk, map_X]; rfl

theorem ι₀_algebraMap (a : k₀) : ι₀ q k₀ K (algebraMap k₀ (CoordRing q k₀) a) = algebraMap K (CoordRing q K) (algebraMap k₀ K a) := by
  change ι₀ q k₀ K (mk q k₀ (C a)) = mk q K (C (algebraMap k₀ K a))
  rw [ι₀_mk, map_C]

theorem ι₀_injective : Function.Injective (ι₀ q k₀ K) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨g, rfl⟩ := mk_surjective q k₀ a
  rw [ι₀_mk] at ha
  change Ideal.Quotient.mk (drinfeldIdeal q K) (MvPolynomial.map (algebraMap k₀ K) g) = 0 at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← map_drinfeldIdeal q k₀ K, ← Ideal.mem_comap,
    MvPolynomial.BaseChangeFF.comap_map_eq] at ha
  change Ideal.Quotient.mk (drinfeldIdeal q k₀) g = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

end CoordRing

section FunctionField

variable (q : ℕ) (k₀ K : Type) [Field k₀] [Field K] [Algebra k₀ K]
  [IsDomain (CoordRing q k₀)] [IsDomain (CoordRing q K)]

noncomputable def j : drinfeldFunctionField q k₀ →+* drinfeldFunctionField q K :=
  IsFractionRing.lift (g := (algebraMap (CoordRing q K) (drinfeldFunctionField q K)).comp (ι₀ q k₀ K))
    ((IsFractionRing.injective (CoordRing q K) (drinfeldFunctionField q K)).comp (ι₀_injective q k₀ K))

theorem j_algebraMap (a : CoordRing q k₀) :
    j q k₀ K (algebraMap (CoordRing q k₀) (drinfeldFunctionField q k₀) a) =
      algebraMap (CoordRing q K) (drinfeldFunctionField q K) (ι₀ q k₀ K a) :=
  IsFractionRing.lift_algebraMap _ a

private theorem _root_.DrinfeldCurve.AJAssembly.algebraMap_mem (k : Type) [Field k] [IsDomain (CoordRing q k)]
    (E : IntermediateField k (drinfeldFunctionField q k))
    (hx : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ∈ E)
    (hy : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ∈ E) (c : CoordRing q k) :
    algebraMap (CoordRing q k) (drinfeldFunctionField q k) c ∈ E := by
  obtain ⟨P, rfl⟩ := mk_surjective q k c
  induction P using MvPolynomial.induction_on with
  | C a =>
    change algebraMap (CoordRing q k) (drinfeldFunctionField q k) (algebraMap k (CoordRing q k) a) ∈ E
    rw [← IsScalarTower.algebraMap_apply]
    exact E.algebraMap_mem a
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact E.add_mem h₁ h₂
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine E.mul_mem hp ?_
    fin_cases i
    · exact hx
    · exact hy

p2m_export "DrinfeldCurve.AJAssembly" "algebraMap_mem"

theorem adjoin_x_y_eq_top (k : Type) [Field k] [IsDomain (CoordRing q k)] :
    IntermediateField.adjoin k ({algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k),
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)} : Set (drinfeldFunctionField q k)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  set E := IntermediateField.adjoin k ({algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k),
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)} : Set (drinfeldFunctionField q k))
  have hx : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ∈ E :=
    IntermediateField.subset_adjoin k _ (Set.mem_insert _ _)
  have hy : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ∈ E :=
    IntermediateField.subset_adjoin k _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := CoordRing q k) z
  exact E.div_mem (algebraMap_mem q k E hx hy a) (algebraMap_mem q k E hx hy b)

end FunctionField

end DrinfeldCurve.AJAssembly

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_algebraMap drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective algHom_ext x y scalePoly_X ofZMod ofZMod_pow_card substPoly_X scalarOf hSubgroup hAction_mk isDomain_coordRing_of_ne_one isCurveOver_drinfeldFunctionField"
namespace AJAssembly
p2m_open "DrinfeldCurve"

theorem apply_j_eq_j_pow (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k]
    [IsDomain (CoordRing q (GaloisField q 2))] [IsDomain (CoordRing q k)]
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    (z : drinfeldFunctionField q (GaloisField q 2)) :
    φ (j q (GaloisField q 2) k z) = j q (GaloisField q 2) k (z ^ q ^ 2) := by
  have hcard : Nat.card (GaloisField q 2) = q ^ 2 := GaloisField.card q 2 two_ne_zero
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite (GaloisField q 2)
  have hcardF : Fintype.card (GaloisField q 2) = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hcard]
  haveI : CharP (drinfeldFunctionField q (GaloisField q 2)) q :=
    (Algebra.charP_iff (GaloisField q 2) (drinfeldFunctionField q (GaloisField q 2)) q).mp inferInstance
  set g₁ : drinfeldFunctionField q (GaloisField q 2) →+* drinfeldFunctionField q k :=
    (φ : drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp (j q (GaloisField q 2) k) with hg₁
  set g₂ : drinfeldFunctionField q (GaloisField q 2) →+* drinfeldFunctionField q k :=
    (j q (GaloisField q 2) k).comp (iterateFrobenius (drinfeldFunctionField q (GaloisField q 2)) q 2) with hg₂
  set ι := algebraMap (CoordRing q (GaloisField q 2)) (drinfeldFunctionField q (GaloisField q 2)) with hι
  have key0 : ((g₁.comp ι).comp (mk q (GaloisField q 2) : MvPolynomial (Fin 2) (GaloisField q 2) →+* _)) =
      ((g₂.comp ι).comp (mk q (GaloisField q 2) : MvPolynomial (Fin 2) (GaloisField q 2) →+* _)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc : (mk q (GaloisField q 2) : MvPolynomial (Fin 2) (GaloisField q 2) →+* CoordRing q (GaloisField q 2))
          (MvPolynomial.C c) = algebraMap (GaloisField q 2) (CoordRing q (GaloisField q 2)) c := rfl
      simp only [RingHom.comp_apply, hc, hg₁, hg₂, hι]
      rw [iterateFrobenius_def, ← map_pow, ← map_pow, ← hcardF, FiniteField.pow_card,
        j_algebraMap, ι₀_algebraMap, ← IsScalarTower.algebraMap_apply k (CoordRing q k)]
      exact φ.commutes _
    · intro i
      simp only [RingHom.comp_apply, hg₁, hg₂, hι, iterateFrobenius_def, map_pow]
      fin_cases i
      · change φ (j q (GaloisField q 2) k (algebraMap _ _ (x q (GaloisField q 2)))) =
          (j q (GaloisField q 2) k (algebraMap _ _ (x q (GaloisField q 2)))) ^ q ^ 2
        rw [j_algebraMap, ι₀_x, hφx]
      · change φ (j q (GaloisField q 2) k (algebraMap _ _ (y q (GaloisField q 2)))) =
          (j q (GaloisField q 2) k (algebraMap _ _ (y q (GaloisField q 2)))) ^ q ^ 2
        rw [j_algebraMap, ι₀_y, hφy]
  have key1 : g₁.comp ι = g₂.comp ι := by
    apply RingHom.ext
    intro a
    obtain ⟨P, rfl⟩ := mk_surjective q (GaloisField q 2) a
    exact RingHom.congr_fun key0 P
  have key : g₁ = g₂ := IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q (GaloisField q 2))) key1
  have hz := RingHom.congr_fun key z
  rw [hg₁, hg₂, RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def] at hz
  exact hz

end DrinfeldCurve.AJAssembly

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField hFunctionFieldAction hFunctionFieldAction_algebraMap drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective algHom_ext x y scalePoly_X ofZMod ofZMod_pow_card substPoly_X scalarOf hSubgroup hAction_mk isDomain_coordRing_of_ne_one isCurveOver_drinfeldFunctionField"
namespace DescAux
p2m_open "DrinfeldCurve"

p2m_open "MvPolynomial P2MW.S_DrinfeldCurve_exists_isCurveOver_adjoin_range_eq_top_apply_hFunctionFieldAction_eq_pow.MvPolynomial"

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]

theorem charP_F : CharP (drinfeldFunctionField q k) q :=
  haveI : CharP k q := charP_of_injective_algebraMap (algebraMap (GaloisField q 2) k).injective q
  charP_of_injective_algebraMap (algebraMap k (drinfeldFunctionField q k)).injective q

theorem algebraMap_scalarOf_pow (u : (GaloisField q 2)ˣ) :
    algebraMap k (drinfeldFunctionField q k) (scalarOf q k u) ^ q ^ 2 =
      algebraMap k (drinfeldFunctionField q k) (scalarOf q k u) := by
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card q 2 two_ne_zero
  rw [scalarOf, ← map_pow, ← map_pow, ← hcard, FiniteField.pow_card]

theorem algebraMap_ofZMod_pow (a : ZMod q) :
    algebraMap k (drinfeldFunctionField q k) (ofZMod q k a) ^ q ^ 2 =
      algebraMap k (drinfeldFunctionField q k) (ofZMod q k a) := by
  rw [← map_pow, pow_two, pow_mul, ofZMod_pow_card, ofZMod_pow_card]

noncomputable def gen (i : Fin 2) : drinfeldFunctionField q k :=
  algebraMap (CoordRing q k) (drinfeldFunctionField q k) (mk q k (X i))

theorem algebraMap_mk (P : MvPolynomial (Fin 2) k) :
    algebraMap (CoordRing q k) (drinfeldFunctionField q k) (mk q k P) = MvPolynomial.aeval (gen q k) P := by
  have key : ((IsScalarTower.toAlgHom k (CoordRing q k) (drinfeldFunctionField q k)).comp (mk q k)) =
      MvPolynomial.aeval (gen q k) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', MvPolynomial.aeval_X, gen]
  exact AlgHom.congr_fun key P

theorem apply_hFunctionFieldAction_comm
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    (h : hSubgroup q) (z : drinfeldFunctionField q k) :
    φ (hFunctionFieldAction q k h z) = hFunctionFieldAction q k h (φ z) := by
  haveI := charP_F q k
  set σ := hFunctionFieldAction q k h with hσ
  have hφgen : ∀ i : Fin 2, φ (gen q k i) = gen q k i ^ q ^ 2 := by
    intro i; fin_cases i
    · exact hφx
    · exact hφy
  set g : Matrix (Fin 2) (Fin 2) (ZMod q) :=
    ((h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 : Matrix (Fin 2) (Fin 2) (ZMod q)) with hg
  set c : k := scalarOf q k (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 with hc

  have hσgen : ∀ j : Fin 2, σ (gen q k j) =
      algebraMap k _ (ofZMod q k (g 0 j)) * (algebraMap k _ c * gen q k 0) +
        algebraMap k _ (ofZMod q k (g 1 j)) * (algebraMap k _ c * gen q k 1) := by
    intro j
    rw [hσ, gen, hFunctionFieldAction_algebraMap, hAction_mk, algebraMap_mk, substPoly_X, Fin.sum_univ_two,
      map_add, map_mul, map_mul, scalePoly_X, scalePoly_X]
    simp only [map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
    rfl
  have hcQ : algebraMap k (drinfeldFunctionField q k) c ^ q ^ 2 = algebraMap k _ c := algebraMap_scalarOf_pow q k _

  have key : ((φ : drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp (((σ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) : drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp
      ((algebraMap (CoordRing q k) (drinfeldFunctionField q k)).comp
        (mk q k : MvPolynomial (Fin 2) k →+* CoordRing q k)))) =
      (((σ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) : drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp ((φ : drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp
      ((algebraMap (CoordRing q k) (drinfeldFunctionField q k)).comp
        (mk q k : MvPolynomial (Fin 2) k →+* CoordRing q k)))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have ha : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (mk q k (C a)) = algebraMap k _ a := by
        rw [algebraMap_mk, MvPolynomial.aeval_C]
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.coe_algHom]
      rw [ha]
      simp only [AlgHom.commutes, AlgEquiv.commutes]
    · intro j
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.coe_algHom]
      change φ (σ (gen q k j)) = σ (φ (gen q k j))
      rw [hφgen, map_pow, hσgen]
      simp only [map_add, map_mul, AlgHom.commutes, hφgen]
      rw [add_pow_char_pow, mul_pow, mul_pow, mul_pow, mul_pow, hcQ, algebraMap_ofZMod_pow, algebraMap_ofZMod_pow]

  have key1 : ((φ : drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp ((σ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) : drinfeldFunctionField q k →+* drinfeldFunctionField q k)).comp
        (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) =
      (((σ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) : drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp (φ : drinfeldFunctionField q k →+* drinfeldFunctionField q k)).comp
        (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) := by
    apply RingHom.ext
    intro a
    obtain ⟨P, rfl⟩ := mk_surjective q k a
    exact RingHom.congr_fun key P
  have key2 := IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q k)) key1
  exact RingHom.congr_fun key2 z

theorem hFunctionFieldAction_pow_card (h : hSubgroup q) :
    hFunctionFieldAction q k h ^ Nat.card (hSubgroup q) = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

end DrinfeldCurve.DescAux

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_exists_isCurveOver_adjoin_range_eq_top_apply_hFunctionFieldAction_eq_pow.DrinfeldCurve in

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
    [IsDomain (CoordRing q k)] [AlgebraicCurve.IsCurveOver k (drinfeldFunctionField q k)]
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    (h : hSubgroup q) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : Algebra (GaloisField q 2) F₁) (_ : Algebra F₁ (drinfeldFunctionField q k))
      (_ : AlgebraicCurve.IsCurveOver (GaloisField q 2) F₁),
      (∃ s : Finset F₁, IntermediateField.adjoin (GaloisField q 2) (s : Set F₁) = ⊤) ∧
      IntermediateField.adjoin k (Set.range (algebraMap F₁ (drinfeldFunctionField q k))) = ⊤ ∧
      ∀ z : F₁, φ (hFunctionFieldAction q k h (algebraMap F₁ (drinfeldFunctionField q k) z)) =
        algebraMap F₁ (drinfeldFunctionField q k) (z ^ Nat.card (GaloisField q 2)) := by
  have hq : q.Prime := Fact.out

  haveI hD₀ : IsDomain (CoordRing q (GaloisField q 2)) := isDomain_coordRing_of_ne_one q hq.ne_one _
  haveI : AlgebraicCurve.IsCurveOver (GaloisField q 2) (drinfeldFunctionField q (GaloisField q 2)) :=
    isCurveOver_drinfeldFunctionField q (GaloisField q 2)
  letI : Algebra (drinfeldFunctionField q (GaloisField q 2)) (drinfeldFunctionField q k) :=
    (AJAssembly.j q (GaloisField q 2) k).toAlgebra
  set x₀ := algebraMap (CoordRing q (GaloisField q 2)) (drinfeldFunctionField q (GaloisField q 2)) (x q (GaloisField q 2))
    with hx₀
  set y₀ := algebraMap (CoordRing q (GaloisField q 2)) (drinfeldFunctionField q (GaloisField q 2)) (y q (GaloisField q 2))
    with hy₀
  have hjx : AJAssembly.j q (GaloisField q 2) k x₀ = algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) := by
    rw [hx₀, AJAssembly.j_algebraMap, AJAssembly.ι₀_x]
  have hjy : AJAssembly.j q (GaloisField q 2) k y₀ = algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) := by
    rw [hy₀, AJAssembly.j_algebraMap, AJAssembly.ι₀_y]
  have hfg : ∃ s : Finset (drinfeldFunctionField q (GaloisField q 2)),
      IntermediateField.adjoin (GaloisField q 2) (s : Set (drinfeldFunctionField q (GaloisField q 2))) = ⊤ := by
    classical
    refine ⟨{x₀, y₀}, ?_⟩
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact AJAssembly.adjoin_x_y_eq_top q (GaloisField q 2)
  have hgen : IntermediateField.adjoin k
      (Set.range (algebraMap (drinfeldFunctionField q (GaloisField q 2)) (drinfeldFunctionField q k))) = ⊤ := by
    rw [eq_top_iff, ← AJAssembly.adjoin_x_y_eq_top q k]
    apply IntermediateField.adjoin.mono
    rintro z (rfl | rfl)
    · exact ⟨x₀, hjx⟩
    · exact ⟨y₀, hjy⟩
  have hcard : Nat.card (GaloisField q 2) = q ^ 2 := GaloisField.card q 2 two_ne_zero
  have hφ : ∀ z : drinfeldFunctionField q (GaloisField q 2),
      φ (algebraMap (drinfeldFunctionField q (GaloisField q 2)) (drinfeldFunctionField q k) z) =
        algebraMap (drinfeldFunctionField q (GaloisField q 2)) (drinfeldFunctionField q k)
          (z ^ Nat.card (GaloisField q 2)) := by
    intro z
    rw [hcard]
    exact AJAssembly.apply_j_eq_j_pow q k φ hφx hφy z

  obtain ⟨F₁, i₁, i₂, i₃, i₄, hfg₁, hgen₁, hφ₁⟩ :=
    AlgebraicCurve.exists_isCurveOver_adjoin_range_eq_top_apply_algEquiv_eq_pow_of_pow_eq_one
      (GaloisField q 2) k (drinfeldFunctionField q (GaloisField q 2)) (drinfeldFunctionField q k)
      hfg hgen φ hφ (hFunctionFieldAction q k h) (Nat.card (hSubgroup q)) Nat.card_pos
      (DescAux.hFunctionFieldAction_pow_card q k h) (DescAux.apply_hFunctionFieldAction_comm q k φ hφx hφy h)
  exact ⟨F₁, i₁, i₂, i₃, i₄, hfg₁, hgen₁, hφ₁⟩

end S_DrinfeldCurve_exists_isCurveOver_adjoin_range_eq_top_apply_hFunctionFieldAction_eq_pow
end P2MW
export P2MW.S_DrinfeldCurve_exists_isCurveOver_adjoin_range_eq_top_apply_hFunctionFieldAction_eq_pow (solution)
