-- Prove2me | solution 1 for DrinfeldCurve.exists_linearEquiv_comp_tateRep_eq_tateRep_pow_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bc7783a5-9efd-5d7f-a455-acefd1665b76

import Mathlib
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_exists_linearEquiv_comp_tateRep_eq_tateRep_pow_comp

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace DrinfeldFrobTwist

open MvPolynomial DrinfeldCurve AlgebraicCurve

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [PerfectField k] [Algebra (GaloisField q 2) k]

omit [PerfectField k] in
theorem charP_k : CharP k q :=
  charP_of_injective_algebraMap (algebraMap (GaloisField q 2) k).injective q

omit [PerfectField k] in
theorem expChar_k : ExpChar k q :=
  haveI := charP_k q k
  ExpChar.prime (Fact.out : q.Prime)

attribute [local instance] expChar_k

def σ : k ≃+* k := frobeniusEquiv k q

theorem σ_apply (a : k) : σ q k a = a ^ q :=
  frobeniusEquiv_apply k q a

theorem σ_ofZMod (a : ZMod q) : σ q k (ofZMod q k a) = ofZMod q k a := by
  rw [σ_apply, ofZMod_pow_card]

theorem σ_scalarOf (α : (GaloisField q 2)ˣ) : σ q k (scalarOf q k α) = scalarOf q k (α ^ q) := by
  rw [σ_apply, scalarOf, scalarOf, Units.val_pow_eq_pow_val, map_pow]

def FrP : MvPolynomial (Fin 2) k ≃+* MvPolynomial (Fin 2) k := mapEquiv (Fin 2) (σ q k)

theorem FrP_apply (f : MvPolynomial (Fin 2) k) : FrP q k f = map (σ q k : k →+* k) f := rfl

theorem FrP_C (a : k) : FrP q k (C a) = C (σ q k a) := by
  rw [FrP_apply, map_C]; rfl

theorem FrP_X (i : Fin 2) : FrP q k (X i) = X i := by
  rw [FrP_apply, map_X]

theorem FrP_drinfeldPoly_sub_one : FrP q k (drinfeldPoly q k - 1) = drinfeldPoly q k - 1 := by
  simp only [drinfeldPoly, map_sub, map_mul, map_pow, FrP_X, map_one]

theorem drinfeldIdeal_eq_map :
    drinfeldIdeal q k = (drinfeldIdeal q k).map (FrP q k : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k) := by
  rw [drinfeldIdeal, Ideal.map_span, Set.image_singleton, RingHom.coe_coe, FrP_drinfeldPoly_sub_one]

def FrC : CoordRing q k ≃+* CoordRing q k :=
  Ideal.quotientEquiv (drinfeldIdeal q k) (drinfeldIdeal q k) (FrP q k) (drinfeldIdeal_eq_map q k)

theorem FrC_mk (f : MvPolynomial (Fin 2) k) : FrC q k (DrinfeldCurve.mk q k f) = DrinfeldCurve.mk q k (FrP q k f) :=
  Ideal.quotientEquiv_mk _ _ _ _ f

local notation "D" => drinfeldFunctionField q k

def FrD : D ≃+* D := IsFractionRing.ringEquivOfRingEquiv (FrC q k)

theorem FrD_algebraMap (a : CoordRing q k) :
    FrD q k (algebraMap (CoordRing q k) D a) = algebraMap (CoordRing q k) D (FrC q k a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem FrD_algebraMap_base (a : k) : FrD q k (algebraMap k D a) = algebraMap k D (σ q k a) := by
  rw [IsScalarTower.algebraMap_apply k (CoordRing q k) D, FrD_algebraMap,
    IsScalarTower.algebraMap_apply k (CoordRing q k) D]
  congr 1
  show FrC q k (DrinfeldCurve.mk q k (C a)) = DrinfeldCurve.mk q k (C (σ q k a))
  rw [FrC_mk, FrP_C]

section Conj

variable {q k}
variable (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) (α : (GaloisField q 2)ˣ)
  (h : (g, α) ∈ hSubgroup q) (h' : (g, α ^ q) ∈ hSubgroup q)

theorem FrP_comp_scale_subst :
    ((FrP q k : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k).comp
        ((scalePoly k (scalarOf q k α)).comp (substPoly q k (g : Matrix (Fin 2) (Fin 2) (ZMod q)))).toRingHom) =
      ((scalePoly k (scalarOf q k (α ^ q))).comp
          (substPoly q k (g : Matrix (Fin 2) (Fin 2) (ZMod q)))).toRingHom.comp
        (FrP q k : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.comp_apply, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, FrP_C]
  · intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.comp_apply, substPoly_X, map_sum, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      scalePoly_X, FrP_C, FrP_X, σ_ofZMod, σ_scalarOf]

include h h' in
theorem FrC_hAction (a : CoordRing q k) :
    FrC q k (hAction q k ⟨(g, α), h⟩ a) = hAction q k ⟨(g, α ^ q), h'⟩ (FrC q k a) := by
  obtain ⟨f, rfl⟩ := mk_surjective q k a
  rw [hAction_mk, FrC_mk, FrC_mk, hAction_mk]
  congr 1
  have := RingHom.congr_fun (FrP_comp_scale_subst g α) f
  simpa using this

include h h' in
theorem FrD_hFunctionFieldAction (x : D) :
    FrD q k (hFunctionFieldAction q k ⟨(g, α), h⟩ x) = hFunctionFieldAction q k ⟨(g, α ^ q), h'⟩ (FrD q k x) := by
  have key : ((FrD q k : D ≃+* D) : D →+* D).comp
        ((hFunctionFieldAction q k ⟨(g, α), h⟩ : D ≃ₐ[k] D) : D →+* D) =
      ((hFunctionFieldAction q k ⟨(g, α ^ q), h'⟩ : D ≃ₐ[k] D) : D →+* D).comp
        ((FrD q k : D ≃+* D) : D →+* D) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q k))
    ext a
    simp only [RingHom.comp_apply, RingHom.coe_coe, hFunctionFieldAction_algebraMap, FrD_algebraMap,
      FrC_hAction g α h h']
  exact RingHom.congr_fun key x

end Conj

variable [IsDomain (CoordRing q k)]

def Φ : SemilinearAut k D :=
  ⟨((FrD q k : D ≃+* D), σ q k), fun a => FrD_algebraMap_base q k a⟩

theorem Φ_smul (x : D) : Φ q k • x = FrD q k x := rfl

variable {q k} in
theorem Φ_mul_ofAlgAut (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) (α : (GaloisField q 2)ˣ)
    (h : (g, α) ∈ hSubgroup q) (h' : (g, α ^ q) ∈ hSubgroup q) :
    Φ q k * SemilinearAut.ofAlgAut (hFunctionFieldAction q k ⟨(g, α), h⟩) =
      SemilinearAut.ofAlgAut (hFunctionFieldAction q k ⟨(g, α ^ q), h'⟩) * Φ q k := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · apply RingEquiv.ext
    intro x
    exact FrD_hFunctionFieldAction g α h h' x
  · show σ q k * 1 = 1 * σ q k
    rw [mul_one, one_mul]

section Tate

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem ofAlgAut_smul_place (τ : F ≃ₐ[K] F) (v : Place K F) :
    SemilinearAut.ofAlgAut τ • v = τ • v := by
  apply Place.ext
  ext x
  rw [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  exact Iff.rfl

theorem ofAlgAut_smul_divisor (τ : F ≃ₐ[K] F) (E : Divisor K F) :
    SemilinearAut.ofAlgAut τ • E = τ • E :=
  have hh : (fun v : Place K F => SemilinearAut.ofAlgAut τ • v) = fun v => τ • v :=
    funext fun v => ofAlgAut_smul_place τ v
  (SemilinearAut.divisor_smul_def _ E).trans
    ((congrArg (Finsupp.mapDomain · E) hh).trans (Divisor.smul_def τ E).symm)

theorem ofAlgAut_smul_pic0 (τ : F ≃ₐ[K] F) (x : Pic0 K F) :
    SemilinearAut.ofAlgAut τ • x = τ • x := by
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective x
  rw [SemilinearAut.pic0_smul_mk, Pic0.smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [SemilinearAut.coe_degZeroSMulHom, Pic0.coe_degZeroSMulHom]
  exact ofAlgAut_smul_divisor τ _

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem rationalGaloisRep_algEquiv_eq (τ : F ≃ₐ[K] F) :
    ModularCurve.rationalGaloisRep ℓ (Pic0 K F) (F ≃ₐ[K] F) τ =
      ModularCurve.rationalGaloisRep ℓ (Pic0 K F) (SemilinearAut K F) (SemilinearAut.ofAlgAut τ) := by
  rw [ModularCurve.rationalGaloisRep_apply, ModularCurve.rationalGaloisRep_apply]

  congr 1

end Tate

variable (ℓ : ℕ) [Fact ℓ.Prime]

local notation "V" => ModularCurve.RationalTateModule ℓ (Pic0 k D)
local notation "ρS" => ModularCurve.rationalGaloisRep ℓ (Pic0 k D) (SemilinearAut k D)
local notation "ρA" => ModularCurve.rationalGaloisRep ℓ (Pic0 k D) (D ≃ₐ[k] D)

def Fr : V ≃ₗ[ℚ_[ℓ]] V :=
  LinearEquiv.ofLinear (ρS (Φ q k)) (ρS (Φ q k)⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; try rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; try rfl)

theorem Fr_coe : ((Fr q k ℓ : V ≃ₗ[ℚ_[ℓ]] V) : V →ₗ[ℚ_[ℓ]] V) = ρS (Φ q k) := rfl

theorem main (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) (α : (GaloisField q 2)ˣ)
    (h : (g, α) ∈ hSubgroup q) (h' : (g, α ^ q) ∈ hSubgroup q) :
    ((Fr q k ℓ : V ≃ₗ[ℚ_[ℓ]] V) : V →ₗ[ℚ_[ℓ]] V) ∘ₗ ρA (hFunctionFieldAction q k ⟨(g, α), h⟩) =
      ρA (hFunctionFieldAction q k ⟨(g, α ^ q), h'⟩) ∘ₗ ((Fr q k ℓ : V ≃ₗ[ℚ_[ℓ]] V) : V →ₗ[ℚ_[ℓ]] V) := by
  rw [Fr_coe, rationalGaloisRep_algEquiv_eq, rationalGaloisRep_algEquiv_eq, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, Φ_mul_ofAlgAut g α h h']

section BaseChange

variable (E : Type*) [Field E] [Algebra ℚ_[ℓ] E]

def FrE : (E ⊗[ℚ_[ℓ]] V) ≃ₗ[E] (E ⊗[ℚ_[ℓ]] V) := LinearEquiv.baseChange ℚ_[ℓ] E V V (Fr q k ℓ)

theorem FrE_coe : ((FrE q k ℓ E : (E ⊗[ℚ_[ℓ]] V) ≃ₗ[E] (E ⊗[ℚ_[ℓ]] V)) : (E ⊗[ℚ_[ℓ]] V) →ₗ[E] (E ⊗[ℚ_[ℓ]] V)) =
    (ρS (Φ q k)).baseChange E := rfl

omit [PerfectField k] in
theorem tateRep_eq (hh : hSubgroup q) :
    tateRep q k ℓ E hh = (ρA (hFunctionFieldAction q k hh)).baseChange E := rfl

theorem mainE (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) (α : (GaloisField q 2)ˣ)
    (h : (g, α) ∈ hSubgroup q) (h' : (g, α ^ q) ∈ hSubgroup q) :
    ((FrE q k ℓ E : (E ⊗[ℚ_[ℓ]] V) ≃ₗ[E] (E ⊗[ℚ_[ℓ]] V)) : (E ⊗[ℚ_[ℓ]] V) →ₗ[E] (E ⊗[ℚ_[ℓ]] V)) ∘ₗ
        tateRep q k ℓ E ⟨(g, α), h⟩ =
      tateRep q k ℓ E ⟨(g, α ^ q), h'⟩ ∘ₗ
        ((FrE q k ℓ E : (E ⊗[ℚ_[ℓ]] V) ≃ₗ[E] (E ⊗[ℚ_[ℓ]] V)) : (E ⊗[ℚ_[ℓ]] V) →ₗ[E] (E ⊗[ℚ_[ℓ]] V)) := by
  rw [FrE_coe, tateRep_eq, tateRep_eq, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← Fr_coe,
    main q k ℓ g α h h']

end BaseChange

end DrinfeldFrobTwist

end

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [PerfectField k] [Algebra (GaloisField q 2) k]
    [IsDomain (DrinfeldCurve.CoordRing q k)] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] :
    ∃ Fr : (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
          (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) ≃ₗ[E]
        (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
          (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))),
      ∀ (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) (α : (GaloisField q 2)ˣ)
        (h : (g, α) ∈ DrinfeldCurve.hSubgroup q) (h' : (g, α ^ q) ∈ DrinfeldCurve.hSubgroup q),
        (Fr : (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) →ₗ[E]
            (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)))) ∘ₗ
            DrinfeldCurve.tateRep q k ℓ E ⟨(g, α), h⟩ =
          DrinfeldCurve.tateRep q k ℓ E ⟨(g, α ^ q), h'⟩ ∘ₗ
            (Fr : (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
                (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) →ₗ[E]
              (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
                (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)))) :=
  ⟨DrinfeldFrobTwist.FrE q k ℓ E, DrinfeldFrobTwist.mainE q k ℓ E⟩

end S_DrinfeldCurve_exists_linearEquiv_comp_tateRep_eq_tateRep_pow_comp
end P2MW
export P2MW.S_DrinfeldCurve_exists_linearEquiv_comp_tateRep_eq_tateRep_pow_comp (solution)
