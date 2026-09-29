-- Prove2me | solution 1 for ExtCitation.Cyclotomic.clGalAction_omegaEigenspace_two_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/14765da7-58fd-5fde-a506-db6bcec29fb6

import Theorems.Thm_ExtCitation_Cyclotomic_thaine_relation_plusField
import Theorems.Thm_NumberField_classGroup_eq_closure_nonSplit_degOne
import Theorems.Thm_ExtCitation_Cyclotomic_omegaIdempotent_two_cycloUnitTwo_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open NumberField JacobiSumStickelberger Stickelberger
open scoped nonZeroDivisors

section TransferSplice
variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

private theorem algebraMap_comp_fractionRingAlgEquiv :
    (algebraMap F K).comp (FractionRing.algEquiv (𝓞 F) F).toRingEquiv.toRingHom =
      (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.toRingHom.comp
        (algebraMap (FractionRing (𝓞 F)) (FractionRing (𝓞 K))) := by
  ext x
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F)
    (FractionRing.algEquiv (𝓞 K) K) x

private theorem finrank_fractionRing_eq :
    Module.finrank (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) = Module.finrank F K :=
  Algebra.finrank_eq_of_equiv_equiv (FractionRing.algEquiv (𝓞 F) F).toRingEquiv
    (FractionRing.algEquiv (𝓞 K) K).toRingEquiv (algebraMap_comp_fractionRingAlgEquiv F K)

private theorem isGalois_fractionRing [IsGalois F K] :
    IsGalois (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) := by
  refine IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv (𝓞 F) F).toRingEquiv.symm)
    (g := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm) <|
      RingHom.ext fun x ↦ IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm
        (FractionRing.algEquiv (𝓞 K) K).symm _

section Galois
variable [IsGalois F K]

private theorem algEquiv_eq_one_or_eq (hdeg : Module.finrank F K = 2) (J : K ≃ₐ[F] K) (hJ : J ≠ 1)
    (φ : K ≃ₐ[F] K) : φ = 1 ∨ φ = J := by
  have hcard : Nat.card (K ≃ₐ[F] K) = 2 := (IsGalois.card_aut_eq_finrank F K).trans hdeg
  by_cases h : φ = 1
  · exact Or.inl h
  · obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[F] K)).mp hcard
    exact Or.inr ((huniq φ h).trans (huniq J hJ).symm)

private theorem ringOfIntegersAlgEquiv_eq_one_or_eq (hdeg : Module.finrank F K = 2) (J : K ≃ₐ[F] K)
    (hJ : J ≠ 1) (σ : 𝓞 K ≃ₐ[𝓞 F] 𝓞 K) :
    σ = 1 ∨ σ = galRestrict (𝓞 F) F K (𝓞 K) J := by
  obtain ⟨φ, rfl⟩ := (galRestrict (𝓞 F) F K (𝓞 K)).surjective σ
  rcases algEquiv_eq_one_or_eq F K hdeg J hJ φ with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr rfl

omit [NumberField K] in
private theorem galRestrict_ne_one (J : K ≃ₐ[F] K) (hJ : J ≠ 1) :
    galRestrict (𝓞 F) F K (𝓞 K) J ≠ 1 := by
  intro h
  apply hJ
  apply (galRestrict (𝓞 F) F K (𝓞 K)).injective
  rw [h, map_one]

private theorem prod_ringOfIntegersAlgEquiv {inst : Fintype (𝓞 K ≃ₐ[𝓞 F] 𝓞 K)} {M : Type*}
    [CommMonoid M] (hdeg : Module.finrank F K = 2) (J : K ≃ₐ[F] K) (hJ : J ≠ 1)
    (f : (𝓞 K ≃ₐ[𝓞 F] 𝓞 K) → M) :
    (@Finset.univ _ inst).prod f = f 1 * f (galRestrict (𝓞 F) F K (𝓞 K) J) := by
  classical
  have huniv : (@Finset.univ _ inst) =
      ({(1 : 𝓞 K ≃ₐ[𝓞 F] 𝓞 K), galRestrict (𝓞 F) F K (𝓞 K) J} : Finset _) := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact ringOfIntegersAlgEquiv_eq_one_or_eq F K hdeg J hJ σ
  rw [huniv, Finset.prod_pair (galRestrict_ne_one F K J hJ).symm]

private theorem algebraMap_intNorm_eq_mul (hdeg : Module.finrank F K = 2) (J : K ≃ₐ[F] K) (hJ : J ≠ 1)
    (x : 𝓞 K) :
    algebraMap (𝓞 F) (𝓞 K) (Algebra.intNorm (𝓞 F) (𝓞 K) x) =
      x * galRestrict (𝓞 F) F K (𝓞 K) J x := by
  have := isGalois_fractionRing F K
  rw [Algebra.algebraMap_intNorm_of_isGalois, prod_ringOfIntegersAlgEquiv F K hdeg J hJ]
  rfl

private theorem exists_pow_eq_span_singleton (I : Ideal (𝓞 K)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, I ^ n = Ideal.span {a} := by
  by_cases hI : I = ⊥
  · exact ⟨1, one_ne_zero, 0, by simp [hI]⟩
  refine ⟨Fintype.card (ClassGroup (𝓞 K)), Fintype.card_ne_zero, ?_⟩
  have hI0 : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  have hIn : I ^ Fintype.card (ClassGroup (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ := pow_mem hI0 _
  have h1 : ClassGroup.mk0 ⟨_, hIn⟩ = 1 := by
    have : (⟨_, hIn⟩ : (Ideal (𝓞 K))⁰) = ⟨I, hI0⟩ ^ Fintype.card (ClassGroup (𝓞 K)) := rfl
    rw [this, map_pow, pow_card_eq_one]
  rw [ClassGroup.mk0_eq_one_iff] at h1
  exact ⟨h1.generator, (Ideal.span_singleton_generator _).symm⟩

private theorem map_relNorm_eq_mul_map (hdeg : Module.finrank F K = 2) (J : K ≃ₐ[F] K) (hJ : J ≠ 1)
    (I : Ideal (𝓞 K)) :
    (Ideal.relNorm (𝓞 F) I).map (algebraMap (𝓞 F) (𝓞 K)) =
      I * I.map (galRestrict (𝓞 F) F K (𝓞 K) J).toRingEquiv := by
  set σ := galRestrict (𝓞 F) F K (𝓞 K) J with hσ
  obtain ⟨n, hn, a, ha⟩ := exists_pow_eq_span_singleton K I
  rw [← pow_left_inj hn, ← Ideal.map_pow, ← map_pow, ha, Ideal.relNorm_singleton, Ideal.map_span,
    Set.image_singleton, algebraMap_intNorm_eq_mul F K hdeg J hJ, mul_pow, ← Ideal.map_pow, ha,
    Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]
  rfl

end Galois
end TransferSplice

namespace ExtCitation
namespace Cyclotomic
p2m_export "ExtCitation.Cyclotomic" "thaine_relation_plusField omegaIdempotent_two_cycloUnitTwo_ne_zero unitsEnd unitsEnd_proj unitsEndHom unitsGalAction omegaIdempotent"
p2m_open "ExtCitation.Cyclotomic ExtCitation"

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in

private theorem isCMField_cyclo (hp5 : 5 ≤ p) : IsCMField (CyclotomicField p ℚ) :=
  IsCyclotomicExtension.Rat.isCMField _ ⟨p, Set.mem_singleton p, by omega⟩

omit [Fact p.Prime] in

private theorem finrank_maximalRealSubfield [IsCMField (CyclotomicField p ℚ)] :
    Module.finrank ↥(maximalRealSubfield (CyclotomicField p ℚ)) (CyclotomicField p ℚ) = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two _ _

private theorem cycloGalEquiv_symm_apply_zeta (d : (ZMod p)ˣ) :
    (cycloGalEquiv p (CyclotomicField p ℚ)).symm d
        (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) =
      IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ ((d : ZMod p)).val := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hspec := hζ.autToPow_spec ℚ ((cycloGalEquiv p (CyclotomicField p ℚ)).symm d)
  have happ : (hζ.autToPow ℚ) ((cycloGalEquiv p (CyclotomicField p ℚ)).symm d) = d := by
    have hcoe : (hζ.autToPow ℚ) ((cycloGalEquiv p (CyclotomicField p ℚ)).symm d) =
        cycloGalEquiv p (CyclotomicField p ℚ)
          ((cycloGalEquiv p (CyclotomicField p ℚ)).symm d) := rfl
    rw [hcoe]
    exact (cycloGalEquiv p (CyclotomicField p ℚ)).apply_symm_apply d
  rw [happ] at hspec
  exact hspec.symm

private theorem zeta_pow_neg_one_val :
    IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ ((-1 : ZMod p)).val =
      (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ))⁻¹ := by
  have hp : p.Prime := Fact.out
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hv : ((-1 : ZMod p)).val + 1 = p := by
    have h0 : ((((-1 : ZMod p)).val + 1 : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
      ring
    have hdvd : p ∣ ((-1 : ZMod p)).val + 1 := (CharP.cast_eq_zero_iff (ZMod p) p _).mp h0
    have hlt : ((-1 : ZMod p)).val < p := ZMod.val_lt _
    have hle : p ≤ ((-1 : ZMod p)).val + 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, hv]
  exact hζ.pow_eq_one

private theorem complexConj_zeta [IsCMField (CyclotomicField p ℚ)] :
    IsCMField.complexConj (CyclotomicField p ℚ)
        (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) =
      (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ))⁻¹ := by
  have hp : p.Prime := Fact.out
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hcard : 0 < Fintype.card (CyclotomicField p ℚ →+* ℂ) := by
    rw [NumberField.Embeddings.card (CyclotomicField p ℚ) ℂ]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := Fintype.card_pos_iff.mp hcard
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have hpow : φ (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) ^ p = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have hnorm : ‖φ (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ))‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow hp.ne_zero
  rw [map_inv₀]
  exact (RCLike.inv_eq_conj hnorm).symm

private theorem cycloGalEquiv_symm_neg_one_eq_conj [IsCMField (CyclotomicField p ℚ)]
    (x : CyclotomicField p ℚ) :
    (cycloGalEquiv p (CyclotomicField p ℚ)).symm (-1) x =
      IsCMField.complexConj (CyclotomicField p ℚ) x := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have key : ((cycloGalEquiv p (CyclotomicField p ℚ)).symm (-1)).toAlgHom =
      ((IsCMField.complexConj (CyclotomicField p ℚ)).toRingEquiv.toRingHom.toRatAlgHom) := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    show (cycloGalEquiv p (CyclotomicField p ℚ)).symm (-1)
        (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) =
      IsCMField.complexConj (CyclotomicField p ℚ)
        (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ))
    rw [cycloGalEquiv_symm_apply_zeta,
      show ((-1 : (ZMod p)ˣ) : ZMod p) = -1 by rw [Units.val_neg, Units.val_one],
      zeta_pow_neg_one_val, complexConj_zeta]
  exact DFunLike.congr_fun key x

private theorem coe_clRingAction (d : (ZMod p)ˣ) (y : 𝓞 (CyclotomicField p ℚ)) :
    (clRingAction p (CyclotomicField p ℚ) d y : CyclotomicField p ℚ) =
      (cycloGalEquiv p (CyclotomicField p ℚ)).symm d (y : CyclotomicField p ℚ) := by
  have h : clRingAction p (CyclotomicField p ℚ) d y =
      galRestrict ℤ ℚ (CyclotomicField p ℚ) (𝓞 (CyclotomicField p ℚ))
        ((cycloGalEquiv p (CyclotomicField p ℚ)).symm d) y := rfl
  rw [h, NumberField.RingOfIntegers.coe_eq_algebraMap, algebraMap_galRestrict_apply]

private theorem clRingAction_neg_one_eq [IsCMField (CyclotomicField p ℚ)] :
    clRingAction p (CyclotomicField p ℚ) (-1) =
      (galRestrict (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ)))
        ↥(maximalRealSubfield (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        (𝓞 (CyclotomicField p ℚ))
        (IsCMField.complexConj (CyclotomicField p ℚ))).toRingEquiv := by
  apply RingEquiv.ext; intro x
  apply NumberField.RingOfIntegers.ext
  rw [coe_clRingAction, cycloGalEquiv_symm_neg_one_eq_conj,
    NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap]
  simp only [AlgEquiv.coe_ringEquiv]
  rw [algebraMap_galRestrict_apply]

private noncomputable def realRestrict
    (σ : CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ) :
    ↥(maximalRealSubfield (CyclotomicField p ℚ)) ≃+*
      ↥(maximalRealSubfield (CyclotomicField p ℚ)) where
  toFun x := ⟨σ x.1, by
    rw [mem_maximalRealSubfield_iff]
    intro φ
    simpa [RingHom.comp_apply] using
      (mem_maximalRealSubfield_iff x.1).mp x.2
        (φ.comp (σ : CyclotomicField p ℚ →+* CyclotomicField p ℚ))⟩
  invFun x := ⟨σ.symm x.1, by
    rw [mem_maximalRealSubfield_iff]
    intro φ
    simpa [RingHom.comp_apply] using
      (mem_maximalRealSubfield_iff x.1).mp x.2
        (φ.comp (σ.symm : CyclotomicField p ℚ →+* CyclotomicField p ℚ))⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.1)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.1)
  map_mul' x y := Subtype.ext (map_mul σ x.1 y.1)
  map_add' x y := Subtype.ext (map_add σ x.1 y.1)

omit [Fact p.Prime] in
@[scoped simp] private theorem realRestrict_apply (σ : CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ)
    (x : ↥(maximalRealSubfield (CyclotomicField p ℚ))) :
    (realRestrict p σ x : CyclotomicField p ℚ) = σ x.1 := rfl

private noncomputable def ΔactE2Fun (d : (ZMod p)ˣ) :
    (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ))) ≃+*
      (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ))) :=
  NumberField.RingOfIntegers.mapRingEquiv
    (realRestrict p ((cycloGalEquiv p (CyclotomicField p ℚ)).symm d))

private theorem ΔactE2Fun_mul (d e : (ZMod p)ˣ) :
    ΔactE2Fun p (d * e) = ΔactE2Fun p d * ΔactE2Fun p e := by
  apply RingEquiv.ext; intro x
  show ΔactE2Fun p (d * e) x = ΔactE2Fun p d (ΔactE2Fun p e x)
  apply NumberField.RingOfIntegers.ext
  simp only [ΔactE2Fun, NumberField.RingOfIntegers.mapRingEquiv_apply]
  apply Subtype.ext
  simp only [realRestrict_apply, map_mul, AlgEquiv.mul_apply]

private noncomputable def ΔactE2 : (ZMod p)ˣ →*
    ((𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ))) ≃+*
      (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ)))) :=
  MonoidHom.mk' (ΔactE2Fun p) (ΔactE2Fun_mul p)

@[scoped simp] private theorem ΔactE2_apply (d : (ZMod p)ˣ) : ΔactE2 p d = ΔactE2Fun p d := rfl

private theorem ΔactE2_spec (d : (ZMod p)ˣ) :
    (algebraMap (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ)))
        (𝓞 (CyclotomicField p ℚ))).comp (ΔactE2 p d).toRingHom =
      (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ)))
          (𝓞 (CyclotomicField p ℚ))) := by
  ext x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [coe_clRingAction]
  rfl

section SplitQuad
variable [IsCMField (CyclotomicField p ℚ)]

omit [Fact p.Prime] [IsCMField (CyclotomicField p ℚ)] in

private theorem absNorm_relNorm_P (𝔓 : Ideal (𝓞 (CyclotomicField p ℚ))) :
    Ideal.absNorm (Ideal.relNorm (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ))) 𝔓) =
      Ideal.absNorm 𝔓 :=
  Ideal.absNorm_relNorm _ _ 𝔓

omit [Fact p.Prime] [IsCMField (CyclotomicField p ℚ)] in

private theorem relNorm_P_isMaximal {ℓ : ℕ} (hℓ : ℓ.Prime)
    (𝔓 : Ideal (𝓞 (CyclotomicField p ℚ))) (hdeg : Ideal.absNorm 𝔓 = ℓ) :
    (Ideal.relNorm (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ))) 𝔓).IsMaximal := by
  have habs : Ideal.absNorm
      (Ideal.relNorm (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ))) 𝔓) = ℓ := by
    rw [absNorm_relNorm_P, hdeg]
  have hprime : (Ideal.relNorm (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ))) 𝔓).IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by rw [habs]; exact hℓ)
  refine hprime.isMaximal ?_
  intro hbot
  rw [hbot] at habs
  simp only [Ideal.absNorm_bot] at habs
  exact hℓ.ne_zero habs.symm

private theorem map_relNorm_P (𝔓 : Ideal (𝓞 (CyclotomicField p ℚ))) :
    (Ideal.relNorm (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ))) 𝔓).map
        (algebraMap (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ)))
          (𝓞 (CyclotomicField p ℚ))) =
      𝔓 * 𝔓.map (clRingAction p (CyclotomicField p ℚ) (-1)) := by
  rw [map_relNorm_eq_mul_map _ _ (finrank_maximalRealSubfield p)
    (IsCMField.complexConj (CyclotomicField p ℚ)) (IsCMField.complexConj_ne_one _) 𝔓,
    ← clRingAction_neg_one_eq]

private theorem complexConj_eq_self_of_mem {x : CyclotomicField p ℚ}
    (hx : x ∈ maximalRealSubfield (CyclotomicField p ℚ)) :
    IsCMField.complexConj (CyclotomicField p ℚ) x = x := by
  have hcard : 0 < Fintype.card (CyclotomicField p ℚ →+* ℂ) := by
    rw [NumberField.Embeddings.card (CyclotomicField p ℚ) ℂ]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := Fintype.card_pos_iff.mp hcard
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  exact (mem_maximalRealSubfield_iff x).mp hx φ

private theorem ΔactE2_neg_one : ΔactE2 p (-1) = RingEquiv.refl _ := by
  apply RingEquiv.ext; intro x
  apply NumberField.RingOfIntegers.ext
  apply Subtype.ext
  show ((realRestrict p ((cycloGalEquiv p (CyclotomicField p ℚ)).symm (-1))
      (x : ↥(maximalRealSubfield (CyclotomicField p ℚ)))) : CyclotomicField p ℚ) =
    ((x : ↥(maximalRealSubfield (CyclotomicField p ℚ))) : CyclotomicField p ℚ)
  rw [realRestrict_apply, cycloGalEquiv_symm_neg_one_eq_conj]
  exact complexConj_eq_self_of_mem p
    (x : ↥(maximalRealSubfield (CyclotomicField p ℚ))).2

private theorem exists_real_unit_of_conj_fixed (u : (𝓞 (CyclotomicField p ℚ))ˣ)
    (hu : Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) (-1)).toMulEquiv u = u) :
    ∃ x₀ : (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ)))ˣ,
      Units.map (algebraMap (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ)))
        (𝓞 (CyclotomicField p ℚ)) : _ →* _) x₀ = u := by
  have h1 : clRingAction p (CyclotomicField p ℚ) (-1) ↑u = ↑u := by
    have := congrArg Units.val hu
    simpa using this
  have hval : (IsCMField.complexConj (CyclotomicField p ℚ))
      ((algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)) ↑u) =
      (algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)) ↑u := by
    have h2 := congrArg
      (fun z : 𝓞 (CyclotomicField p ℚ) => (z : CyclotomicField p ℚ)) h1
    beta_reduce at h2
    rw [coe_clRingAction, cycloGalEquiv_symm_neg_one_eq_conj] at h2
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact h2
  obtain ⟨v, hv⟩ :=
    (IsCMField.Units.complexConj_eq_self_iff (CyclotomicField p ℚ) u).mp hval
  refine ⟨v, Units.ext ?_⟩
  apply NumberField.RingOfIntegers.ext
  rw [Units.coe_map]
  calc ((algebraMap (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ)))
        (𝓞 (CyclotomicField p ℚ)) ↑v : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ)
      = algebraMap (𝓞 ↥(maximalRealSubfield (CyclotomicField p ℚ)))
          (CyclotomicField p ℚ) ↑v := rfl
    _ = algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) ↑u := hv
    _ = ((↑u : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) := rfl

end SplitQuad

end ExtCitation.Cyclotomic
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation"

namespace ExtCitation
namespace Cyclotomic
p2m_export "ExtCitation.Cyclotomic" "thaine_relation_plusField omegaIdempotent_two_cycloUnitTwo_ne_zero unitsEnd unitsEnd_proj unitsEndHom unitsGalAction omegaIdempotent"
p2m_open "ExtCitation.Cyclotomic ExtCitation"

p2m_open "Polynomial NumberField Ideal NumberField.Ideal JacobiSumStickelberger Stickelberger"
open scoped nonZeroDivisors

variable (p : ℕ) [hp : Fact p.Prime]

local notation3 "K" => CyclotomicField p ℚ

set_option backward.isDefEq.respectTransparency false in

private noncomputable scoped instance instIsCycExtB : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  inferInstance

private abbrev KumField (a : K) : Type := (X ^ p - C a).SplittingField

private scoped instance (a : K) : NumberField (KumField p a) :=
  NumberField.of_module_finite K (KumField p a)

private theorem primitiveRoots_nonempty : (primitiveRoots p K).Nonempty :=
  ⟨IsCyclotomicExtension.zeta p ℚ K,
    (mem_primitiveRoots hp.out.pos).mpr (IsCyclotomicExtension.zeta_spec p ℚ K)⟩

private theorem irreducible_of_not_pow {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ p - C a) :=
  X_pow_sub_C_irreducible_of_prime hp.out ha

private theorem isGalois_kumField {a : K} (ha : ∀ b : K, b ^ p ≠ a) : IsGalois K (KumField p a) :=
  isGalois_of_isSplittingField_X_pow_sub_C (primitiveRoots_nonempty p)
    (irreducible_of_not_pow p ha) (KumField p a)

private theorem finrank_kumField {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Module.finrank K (KumField p a) = p :=
  finrank_of_isSplittingField_X_pow_sub_C (primitiveRoots_nonempty p)
    (irreducible_of_not_pow p ha) (KumField p a)

private theorem natCast_not_mem_of_absNorm_eq {𝔓 : Ideal (𝓞 K)} (h𝔓 : 𝔓 ≠ ⊤)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hN : absNorm 𝔓 = ℓ) : (p : 𝓞 K) ∉ 𝔓 := by
  intro hpm
  have hℓm : (ℓ : 𝓞 K) ∈ 𝔓 := by simpa [hN] using Ideal.absNorm_mem 𝔓
  have hcop : IsCoprime (ℓ : 𝓞 K) (p : 𝓞 K) := by
    have h := (Nat.coprime_primes hℓ hp.out).mpr hℓp
    have h' : IsCoprime (ℓ : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    simpa using h'.map (algebraMap ℤ (𝓞 K))
  obtain ⟨u, v, huv⟩ := hcop
  apply h𝔓
  rw [Ideal.eq_top_iff_one, ← huv]
  exact 𝔓.add_mem (𝔓.mul_mem_left u hℓm) (𝔓.mul_mem_left v hpm)

private theorem zeta_sub_one_not_mem {𝔓 : Ideal (𝓞 K)} (hp𝔓 : (p : 𝓞 K) ∉ 𝔓) :
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1 ∉ 𝔓 := by
  intro h
  apply hp𝔓
  have hK' : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    rw [zero_add, pow_one]; exact instIsCycExtB p
  have hζ' : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    rw [zero_add, pow_one]; exact IsCyclotomicExtension.zeta_spec p ℚ K
  have hpmem := IsCyclotomicExtension.Rat.p_mem_span_zeta_sub_one p 0 hζ'
  exact (Ideal.span_singleton_le_iff_mem _).mpr h (by simpa using hpmem)

private theorem mk0_eq_one_of_absNorm_eq_p (𝔓 : (Ideal (𝓞 K))⁰) (hmax : (𝔓 : Ideal (𝓞 K)).IsMaximal)
    (hN : absNorm (𝔓 : Ideal (𝓞 K)) = p) : ClassGroup.mk0 𝔓 = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  haveI : (𝔓 : Ideal (𝓞 K)).IsPrime := hmax.isPrime
  haveI : (𝔓 : Ideal (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    have hle : Ideal.span {(p : ℤ)} ≤ (𝔓 : Ideal (𝓞 K)).under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
      simpa [hN] using Ideal.absNorm_mem (𝔓 : Ideal (𝓞 K))
    refine (Int.ideal_span_isMaximal_of_prime p).eq_of_le ?_ hle
    exact Ideal.comap_ne_top _ hmax.ne_top
  have h := IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p K hζ (𝔓 : Ideal (𝓞 K))
  rw [ClassGroup.mk0_eq_one_iff]
  exact ⟨⟨hζ.toInteger - 1, by rw [h]⟩⟩

section Split

open scoped Pointwise in

private theorem ncard_primesOver_kumField (a : 𝓞 K) (ha : ∀ b : K, b ^ p ≠ (a : K))
    (𝔓 : Ideal (𝓞 K)) [hmax : 𝔓.IsMaximal]
    (hp𝔓 : (p : 𝓞 K) ∉ 𝔓) (ha𝔓 : a ∉ 𝔓) (y : 𝓞 K) (hy : a - y ^ p ∈ 𝔓) :
    (𝔓.primesOver (𝓞 (KumField p (a : K)))).ncard = p := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hprim : (primitiveRoots p K).Nonempty := primitiveRoots_nonempty p
  have H : Irreducible (X ^ p - C (a : K)) := irreducible_of_not_pow p ha
  haveI : IsGalois K (KumField p (a : K)) := isGalois_kumField p ha
  have hdeg : Module.finrank K (KumField p (a : K)) = p := finrank_kumField p ha
  have h𝔓bot : 𝔓 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmax
    (RingOfIntegers.not_isField K)

  have hfi := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔓 (𝓞 (KumField p (a : K)))
    ((KumField p (a : K)) ≃ₐ[K] (KumField p (a : K)))
  rw [IsGaloisGroup.card_eq_finrank ((KumField p (a : K)) ≃ₐ[K] (KumField p (a : K))) K (KumField p (a : K)), hdeg] at hfi
  have hdvd : (𝔓.primesOver (𝓞 (KumField p (a : K)))).ncard ∣ p := Dvd.intro _ hfi
  rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | hpp
  swap
  · exact hpp
  exfalso

  obtain ⟨𝔐, h𝔐⟩ := Set.ncard_eq_one.mp h1
  have h𝔐mem : 𝔐 ∈ 𝔓.primesOver (𝓞 (KumField p (a : K))) := by rw [h𝔐]; exact Set.mem_singleton 𝔐
  haveI h𝔐prime : 𝔐.IsPrime := h𝔐mem.1
  haveI h𝔐over : 𝔐.LiesOver 𝔓 := h𝔐mem.2
  have hunder : 𝔓 = 𝔐.comap (algebraMap (𝓞 K) (𝓞 (KumField p (a : K)))) := h𝔐over.over

  set β : (KumField p (a : K)) := rootOfSplitsXPowSubC (NeZero.pos p) (a : K) (KumField p (a : K)) with hβdef
  have hβ : β ^ p = algebraMap K (KumField p (a : K)) (a : K) := rootOfSplitsXPowSubC_pow (a : K) (KumField p (a : K))
  have hβint : IsIntegral ℤ β := by
    refine IsIntegral.of_pow hp.out.pos ?_
    rw [hβ]
    exact (map_isIntegral_int (algebraMap K (KumField p (a : K))) a.isIntegral_coe)
  set βi : 𝓞 (KumField p (a : K)) := ⟨β, hβint⟩ with hβidef
  have hβi : βi ^ p = algebraMap (𝓞 K) (𝓞 (KumField p (a : K))) a := by
    apply RingOfIntegers.ext
    calc ((βi ^ p : 𝓞 (KumField p (a : K))) : (KumField p (a : K))) = β ^ p := by
            change algebraMap (𝓞 (KumField p (a : K))) (KumField p (a : K)) (βi ^ p) = β ^ p
            rw [map_pow]; rfl
      _ = algebraMap K (KumField p (a : K)) (a : K) := hβ
      _ = algebraMap (𝓞 K) (KumField p (a : K)) a := (IsScalarTower.algebraMap_apply (𝓞 K) K (KumField p (a : K)) a).symm
      _ = ((algebraMap (𝓞 K) (𝓞 (KumField p (a : K))) a : 𝓞 (KumField p (a : K))) : (KumField p (a : K))) := IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 (KumField p (a : K))) (KumField p (a : K)) a

  set τ : (KumField p (a : K)) ≃ₐ[K] (KumField p (a : K)) := (autEquivZmod H (KumField p (a : K)) hζ).symm (Multiplicative.ofAdd (1 : ZMod p)) with hτdef
  have hτβ : τ β = (IsCyclotomicExtension.zeta p ℚ K) • β := by
    have := autEquivZmod_symm_apply_natCast H (KumField p (a : K)) hβ hζ 1
    simpa only [Nat.cast_one, pow_one] using this
  have hτβi : τ • βi = algebraMap (𝓞 K) (𝓞 (KumField p (a : K))) hζ.toInteger * βi := by
    apply Subtype.ext
    change τ β = _
    rw [hτβ, Algebra.smul_def]
    rfl

  have hτ𝔐 : τ • 𝔐 = 𝔐 := by
    have hmem : (τ • 𝔐) ∈ 𝔓.primesOver (𝓞 (KumField p (a : K))) := ⟨inferInstance, inferInstance⟩
    rw [h𝔐] at hmem
    exact hmem

  have hι𝔐 : ∀ z : 𝓞 K, algebraMap (𝓞 K) (𝓞 (KumField p (a : K))) z ∈ 𝔐 → z ∈ 𝔓 := by
    intro z hz
    rw [hunder]
    exact hz
  have hζ1 : algebraMap (𝓞 K) (𝓞 (KumField p (a : K))) hζ.toInteger - 1 ∉ 𝔐 := by
    intro h
    refine zeta_sub_one_not_mem p hp𝔓 (hι𝔐 _ ?_)
    simpa using h
  have hβ𝔐 : βi ∉ 𝔐 := by
    intro h
    apply ha𝔓
    apply hι𝔐
    rw [← hβi]
    exact 𝔐.pow_mem_of_mem h p hp.out.pos

  set π := Ideal.Quotient.mk 𝔐 with hπdef
  set ι := algebraMap (𝓞 K) (𝓞 (KumField p (a : K))) with hιdef
  have hζF : IsPrimitiveRoot (π (ι hζ.toInteger)) p := by
    have hpow : π (ι hζ.toInteger) ^ p = 1 := by
      rw [← map_pow, ← map_pow]
      have : hζ.toInteger ^ p = 1 := by
        apply RingOfIntegers.ext
        rw [RingOfIntegers.coe_eq_algebraMap, map_pow, RingOfIntegers.coe_eq_algebraMap, map_one]
        exact hζ.pow_eq_one
      rw [this, map_one, map_one]
    have hne : π (ι hζ.toInteger) ≠ 1 := by
      intro h
      apply hζ1
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ← hπdef, h, sub_self]
    have hord := orderOf_eq_prime hpow hne
    exact ⟨hpow, fun l hl => hord ▸ orderOf_dvd_of_pow_eq_one hl⟩
  have hprod := X_pow_sub_C_eq_prod hζF hp.out.pos (rfl : (π (ι y)) ^ p = (π (ι y)) ^ p)
  have heval : (∏ i ∈ Finset.range p, (π βi - π (ι hζ.toInteger) ^ i * π (ι y))) = 0 := by
    have h := congrArg (Polynomial.eval (π βi)) hprod
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at h
    rw [← h, ← map_pow, hβi, ← map_pow, ← map_pow, ← map_sub, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    rw [hunder] at hy
    exact hy
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp heval

  have hmem1 : βi - ι (hζ.toInteger ^ i * y) ∈ 𝔐 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hπdef, map_mul, map_pow, map_mul, map_pow]
    exact hi

  have hmem2 : ι hζ.toInteger * βi - ι (hζ.toInteger ^ i * y) ∈ 𝔐 := by
    have h := Ideal.smul_mem_pointwise_smul τ _ 𝔐 hmem1
    rw [hτ𝔐, smul_sub, hτβi] at h
    have hfix : τ • ι (hζ.toInteger ^ i * y) = ι (hζ.toInteger ^ i * y) := by
      apply Subtype.ext
      exact τ.commutes _
    rwa [hfix] at h
  have hmem3 : (ι hζ.toInteger - 1) * βi ∈ 𝔐 := by
    have := 𝔐.sub_mem hmem2 hmem1
    convert this using 1
    ring
  rcases h𝔐prime.mem_or_mem hmem3 with h | h
  · exact hζ1 h
  · exact hβ𝔐 h

private theorem not_pow_residue_of_not_isSplitPrime (a : 𝓞 K) (ha : ∀ b : K, b ^ p ≠ (a : K))
    (𝔓 : Ideal (𝓞 K)) (hmax : 𝔓.IsMaximal)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hN : absNorm 𝔓 = ℓ) (hau : IsUnit a)
    (hns : ¬ NumberField.IsSplitPrime K (KumField p (a : K)) 𝔓) (y : 𝓞 K) :
    a - y ^ p ∉ 𝔓 := by
  intro hy
  have hp𝔓 : (p : 𝓞 K) ∉ 𝔓 := natCast_not_mem_of_absNorm_eq p hmax.ne_top hℓ hℓp hN
  have ha𝔓 : a ∉ 𝔓 := fun h => hmax.ne_top (Ideal.eq_top_of_isUnit_mem 𝔓 h hau)
  haveI := hmax
  exact hns ⟨hmax, hN ▸ hℓ, by
    change (𝔓.primesOver _).ncard = _
    rw [ncard_primesOver_kumField p a ha 𝔓 hp𝔓 ha𝔓 y hy, finrank_kumField p ha]⟩

end Split
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

open NumberField JacobiSumStickelberger Stickelberger

section Idempotent

variable {A : Type*} [AddCommGroup A] [Module (ZMod p) A]

private theorem act_omegaIdempotent (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) (i : ℕ) (d : (ZMod p)ˣ)
    (x : A) :
    ρ d (omegaIdempotent p ρ i x) = ((d : ZMod p) ^ i) • omegaIdempotent p ρ i x := by
  simp only [omegaIdempotent, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    map_smul, map_sum]
  rw [smul_comm ((d : ZMod p) ^ i)]
  congr 1
  rw [Finset.smul_sum]

  refine Fintype.sum_equiv (Equiv.mulLeft d) _ _ fun d' => ?_
  simp only [Equiv.coe_mulLeft]
  rw [← Module.End.mul_apply, ← map_mul, smul_smul]
  congr 1
  have hd : ((d : ZMod p)) ^ i ≠ 0 := pow_ne_zero _ d.ne_zero
  rw [Units.val_mul, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

private theorem omegaIdempotent_act (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) (i : ℕ) (d : (ZMod p)ˣ)
    (x : A) :
    omegaIdempotent p ρ i (ρ d x) = ρ d (omegaIdempotent p ρ i x) := by
  simp only [omegaIdempotent, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply (ρ d), ← map_mul, mul_comm]

private theorem omegaIdempotent_apply_of_isOmegaEigenvector (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A)
    (i : ℕ) (a : A) (ha : IsOmegaEigenvector ρ i a) : omegaIdempotent p ρ i a = a := by
  have h : ∀ d : (ZMod p)ˣ, ((d : ZMod p) ^ i)⁻¹ • ρ d a = a := by
    intro d
    rw [ha d, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ d.ne_zero), one_smul]
  simp only [omegaIdempotent, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, h,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul,
    inv_mul_cancel₀, one_smul]
  rw [Nat.card_eq_fintype_card, ZMod.card_units p, Nat.cast_sub hp.out.one_le, ZMod.natCast_self,
    Nat.cast_one, zero_sub, neg_ne_zero]
  exact one_ne_zero

end Idempotent
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

section Lift

variable {R : Type*} [CommRing R]

private theorem eigen_lift (act : (ZMod p)ˣ →* (R ≃+* R)) (x : ModP p (Additive Rˣ)) (δ : Rˣ)
    (hδ : ModP.proj p (Additive Rˣ) (Additive.ofMul δ) =
      omegaIdempotent p ((unitsEndHom p R).comp act) 2 x) (d : (ZMod p)ˣ) :
    ∃ v : Rˣ, Units.mapEquiv (act d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have h1 : ModP.proj p (Additive Rˣ) (Additive.ofMul (Units.mapEquiv (act d).toMulEquiv δ)) =
      ModP.proj p (Additive Rˣ) (Additive.ofMul (δ ^ ((d : ZMod p) ^ 2).val)) := by
    rw [← unitsEnd_proj, hδ]
    change ((unitsEndHom p R).comp act d) (omegaIdempotent p ((unitsEndHom p R).comp act) 2 x) = _
    rw [act_omegaIdempotent, ← hδ, ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p),
      ZMod.natCast_zmod_val]
  rw [← sub_eq_zero, ← map_sub, ModP.proj_eq_zero_iff] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨Additive.toMul y, ?_⟩
  rw [← ofMul_div] at hy
  have hy' : (Additive.toMul y) ^ p = Units.mapEquiv (act d).toMulEquiv δ / δ ^ ((d : ZMod p) ^ 2).val := by
    have := congrArg Additive.toMul hy
    simpa using this
  rw [eq_div_iff_mul_eq'] at hy'
  rw [← hy', mul_comm]

end Lift
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

section Delta

private noncomputable def unitsModPMap {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) :
    ModP p (Additive Sˣ) →ₗ[ZMod p] ModP p (Additive Tˣ) :=
  have : NeZero p := ⟨hp.out.ne_zero⟩
  (QuotientAddGroup.map (nsmulRange p (Additive Sˣ)) (nsmulRange p (Additive Tˣ))
    (MonoidHom.toAdditive (Units.map (f : S →* T))) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨MonoidHom.toAdditive (Units.map (f : S →* T)) x, (map_nsmul _ _ _).symm⟩)).toZModLinearMap p

@[scoped simp] private lemma unitsModPMap_proj {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (u : Sˣ) :
    unitsModPMap p f (ModP.proj p (Additive Sˣ) (Additive.ofMul u)) =
      ModP.proj p (Additive Tˣ) (Additive.ofMul (Units.map (f : S →* T) u)) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rfl

private theorem exists_delta (hp5 : 5 ≤ p)
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [Algebra Kplus K]
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 K)).comp
      (Δact d).toRingHom = (clRingAction p K d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 K)))
    (ζ : 𝓞 K) (hζ : IsPrimitiveRoot (ζ : K) p)
    (c₂ : (𝓞 K)ˣ) (hc : (c₂ : 𝓞 K) = 1 + ζ)
    (x₀ : (𝓞 Kplus)ˣ)
    (hx₀ : Units.map (algebraMap (𝓞 Kplus) (𝓞 K) : 𝓞 Kplus →* 𝓞 K) x₀ =
      c₂ * Units.mapEquiv (clRingAction p K (-1)).toMulEquiv c₂) :
    ∃ δ : (𝓞 Kplus)ˣ,
      (∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
        Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p) ∧
      ∀ b : K, b ^ p ≠ ((algebraMap (𝓞 Kplus) (𝓞 K) (δ : 𝓞 Kplus) : 𝓞 K) : K) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩

  set ρ' : (ZMod p)ˣ →* Module.End (ZMod p) (ModP p (Additive (𝓞 Kplus)ˣ)) :=
    (unitsEndHom p (𝓞 Kplus)).comp Δact with hρ'
  set u : ModP p (Additive (𝓞 Kplus)ˣ) :=
    omegaIdempotent p ρ' 2 (ModP.proj p _ (Additive.ofMul x₀)) with hu
  obtain ⟨δa, hδa⟩ := ModP.proj_surjective p (Additive (𝓞 Kplus)ˣ) u
  refine ⟨Additive.toMul δa, fun d => eigen_lift p Δact _ _ (by simpa using hδa) d, ?_⟩

  intro b hb
  set f : 𝓞 Kplus →+* 𝓞 K := algebraMap (𝓞 Kplus) (𝓞 K) with hf
  set ι := unitsModPMap p f with hι

  have hnat : ∀ (d : (ZMod p)ˣ) (w : ModP p (Additive (𝓞 Kplus)ˣ)),
      ι (ρ' d w) = unitsGalAction p d (ι w) := by
    intro d w
    obtain ⟨w, rfl⟩ := ModP.proj_surjective p _ w
    change ι (unitsEnd p (𝓞 Kplus) (Δact d) (ModP.proj p _ (Additive.ofMul (Additive.toMul w)))) =
      unitsEnd p (𝓞 K) (clRingAction p K d) (ι (ModP.proj p _ (Additive.ofMul (Additive.toMul w))))
    rw [unitsEnd_proj, hι, unitsModPMap_proj, unitsModPMap_proj, unitsEnd_proj]
    congr 2
    apply Units.ext
    have h := congrArg (fun g : 𝓞 Kplus →+* 𝓞 K => g (Additive.toMul w : (𝓞 Kplus)ˣ)) (hΔact d)
    simpa using h

  have hιe : ∀ w, ι (omegaIdempotent p ρ' 2 w) = omegaIdempotent p (unitsGalAction p) 2 (ι w) := by
    intro w
    simp only [omegaIdempotent, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
      map_smul, map_sum, hnat]

  have hιx₀ : ι (ModP.proj p _ (Additive.ofMul x₀)) =
      ModP.proj p _ (Additive.ofMul c₂) + unitsGalAction p (-1) (ModP.proj p _ (Additive.ofMul c₂)) := by
    rw [hι, unitsModPMap_proj, hx₀, ofMul_mul, map_add]
    rfl

  have he2 : omegaIdempotent p (unitsGalAction p) 2 (ι (ModP.proj p _ (Additive.ofMul x₀))) =
      (2 : ZMod p) • omegaIdempotent p (unitsGalAction p) 2 (ModP.proj p _ (Additive.ofMul c₂)) := by
    rw [hιx₀, map_add, omegaIdempotent_act, act_omegaIdempotent, two_smul]
    congr 1
    simp

  have hzero : omegaIdempotent p (unitsGalAction p) 2 (ι (ModP.proj p _ (Additive.ofMul x₀))) = 0 := by
    rw [← hιe, ← hu, ← hδa]
    change ι (ModP.proj p _ (Additive.ofMul (Additive.toMul δa))) = 0
    rw [hι, unitsModPMap_proj, ModP.proj_eq_zero_iff]

    have hbint : IsIntegral ℤ b := by
      refine IsIntegral.of_pow hp.out.pos ?_
      rw [hb]
      exact RingOfIntegers.isIntegral_coe _
    set bi : 𝓞 K := ⟨b, hbint⟩ with hbi
    have hbip : bi ^ p = f (Additive.toMul δa : (𝓞 Kplus)ˣ) := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 K) K (bi ^ p) = _
      rw [map_pow]
      exact hb
    have hbu : IsUnit bi := by
      have : IsUnit (bi ^ p) := by
        rw [hbip]
        exact (Units.map (f : 𝓞 Kplus →* 𝓞 K) (Additive.toMul δa)).isUnit
      exact (isUnit_pow_iff hp.out.ne_zero).mp this
    refine ⟨Additive.ofMul hbu.unit, ?_⟩
    rw [← ofMul_pow]
    congr 1
    ext
    simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.coe_map, MonoidHom.coe_coe, hbip]
  rw [hzero] at he2
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ¬ p ∣ 2 := fun h => by
      have := Nat.le_of_dvd two_pos h
      omega
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr this
  have := (smul_eq_zero.mp he2.symm).resolve_left h2
  exact omegaIdempotent_two_cycloUnitTwo_ne_zero p hp5 ζ hζ c₂ hc this

end Delta
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

section Glue

private theorem exists_cycloUnit₂ (hp3 : 3 ≤ p) :
    ∃ c₂ : (𝓞 K)ˣ, (c₂ : 𝓞 K) = 1 + (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger := by
  have hζi := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot
  have hcop : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (by omega)
  have hu := hζi.geom_sum_isUnit (by omega) hcop
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one] at hu
  exact ⟨hu.unit, hu.unit_spec⟩

private theorem mapEquiv_neg_one_mul_self (u : (𝓞 K)ˣ) :
    Units.mapEquiv (clRingAction p K (-1)).toMulEquiv
        (u * Units.mapEquiv (clRingAction p K (-1)).toMulEquiv u) =
      u * Units.mapEquiv (clRingAction p K (-1)).toMulEquiv u := by
  have hsq : clRingAction p K (-1) * clRingAction p K (-1) = 1 := by
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  have h2 : ∀ x : 𝓞 K,
      (clRingAction p K (-1)).toMulEquiv ((clRingAction p K (-1)).toMulEquiv x) = x := fun x => by
    change (clRingAction p K (-1) * clRingAction p K (-1)) x = x
    rw [hsq]
    rfl
  apply Units.ext
  simp only [map_mul, Units.coe_mapEquiv, Units.val_mul, h2]
  rw [mul_comm]

private theorem mk_not_mem_pow_of_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    (𝔏 : Ideal S) (𝔓 : Ideal T) (hle : 𝔏 ≤ 𝔓.comap f) (δ : S) (n : ℕ)
    (h : ∀ y : T, f δ - y ^ n ∉ 𝔓) :
    Ideal.Quotient.mk 𝔏 δ ∉ {x : S ⧸ 𝔏 | ∃ y, y ^ n = x} := by
  rintro ⟨yb, hyb⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  rw [← map_pow, Ideal.Quotient.eq] at hyb
  have h1 : f (y ^ n - δ) ∈ 𝔓 := hle hyb
  apply h (f y)
  rw [map_sub, map_pow] at h1
  simpa using 𝔓.neg_mem h1

private theorem delta_package (hp5 : 5 ≤ p)
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [Algebra Kplus K]
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 K)).comp
      (Δact d).toRingHom = (clRingAction p K d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 K)))
    (hdesc : ∀ u : (𝓞 K)ˣ, Units.mapEquiv (clRingAction p K (-1)).toMulEquiv u = u →
      ∃ x₀ : (𝓞 Kplus)ˣ, Units.map (algebraMap (𝓞 Kplus) (𝓞 K) : 𝓞 Kplus →* 𝓞 K) x₀ = u) :
    ∃ δ : (𝓞 Kplus)ˣ,
      (∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
        Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p) ∧
      ∀ b : K, b ^ p ≠ ((algebraMap (𝓞 Kplus) (𝓞 K) (δ : 𝓞 Kplus) : 𝓞 K) : K) := by
  obtain ⟨c₂, hc⟩ := exists_cycloUnit₂ p (by omega)
  obtain ⟨x₀, hx₀⟩ := hdesc _ (mapEquiv_neg_one_mul_self p c₂)
  exact exists_delta p hp5 Kplus Δact hΔact _ (IsCyclotomicExtension.zeta_spec p ℚ K) c₂ hc x₀ hx₀

private theorem hδ𝔏_of_not_isSplitPrime
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [Algebra Kplus K]
    (δ : (𝓞 Kplus)ˣ)
    (hδ : ∀ b : K, b ^ p ≠ ((algebraMap (𝓞 Kplus) (𝓞 K) (δ : 𝓞 Kplus) : 𝓞 K) : K))
    (𝔓 : Ideal (𝓞 K)) (hmax : 𝔓.IsMaximal) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hN : absNorm 𝔓 = ℓ)
    (hns : ¬ NumberField.IsSplitPrime K
      (KumField p ((algebraMap (𝓞 Kplus) (𝓞 K) (δ : 𝓞 Kplus) : 𝓞 K) : K)) 𝔓)
    (𝔏 : Ideal (𝓞 Kplus)) (hle : 𝔏 ≤ 𝔓.comap (algebraMap (𝓞 Kplus) (𝓞 K))) :
    Ideal.Quotient.mk 𝔏 (δ : 𝓞 Kplus) ∉ {x : 𝓞 Kplus ⧸ 𝔏 | ∃ y, y ^ p = x} :=
  mk_not_mem_pow_of_map (algebraMap (𝓞 Kplus) (𝓞 K)) 𝔏 𝔓 hle _ p
    (not_pow_residue_of_not_isSplitPrime p _ hδ 𝔓 hmax hℓ hℓp hN
      (Units.map (algebraMap (𝓞 Kplus) (𝓞 K) : 𝓞 Kplus →* 𝓞 K) δ).isUnit hns)

end Glue
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

end ExtCitation.Cyclotomic
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

namespace ExtCitation
namespace Cyclotomic
p2m_export "ExtCitation.Cyclotomic" "thaine_relation_plusField omegaIdempotent_two_cycloUnitTwo_ne_zero unitsEnd unitsEnd_proj unitsEndHom unitsGalAction omegaIdempotent"
p2m_open "ExtCitation.Cyclotomic ExtCitation"

section Idempotent

variable (p : ℕ) [hp : Fact p.Prime]
variable {A : Type*} [AddCommGroup A] [Module (ZMod p) A]

private lemma card_units_cast_eq_neg_one : (Nat.card (ZMod p)ˣ : ZMod p) = -1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units, Nat.cast_sub hp.out.one_lt.le,
    Nat.cast_one, CharP.cast_eq_zero, zero_sub]

private lemma card_units_cast_ne_zero : (Nat.card (ZMod p)ˣ : ZMod p) ≠ 0 := by
  rw [card_units_cast_eq_neg_one]; exact neg_ne_zero.mpr one_ne_zero

private theorem sum_tinv_smul_eq (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) (i : ℕ)
    (t : ZMod p) (a : A) :
    (∑ d : (ZMod p)ˣ, (t * ((d : ZMod p) ^ i)⁻¹) • ρ d a) =
      (-t) • omegaIdempotent p ρ i a := by
  simp only [omegaIdempotent, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun d _ => by
    congr 1; rw [card_units_cast_eq_neg_one]; ring

private theorem val_nsmul_eq (n : ZMod p) (a : A) : n.val • a = n • a := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_val, ZMod.cast_id]

private theorem addHom_eq_zero_of_closure_eq_top {G : Type*} [CommGroup G]
    (f : Additive G →+ A) (S : Set G) (hS : (⊤ : Subgroup G) = Subgroup.closure S)
    (hf : ∀ c ∈ S, f (Additive.ofMul c) = 0) (a : G) :
    f (Additive.ofMul a) = 0 := by
  have ha : a ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top a
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hf x hx
  | one => exact f.map_zero
  | mul x y _ _ hx hy =>
    rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y from rfl,
      f.map_add, hx, hy, add_zero]
  | inv x _ hx =>
    rw [show Additive.ofMul x⁻¹ = -Additive.ofMul x from rfl, map_neg, hx, neg_zero]

private theorem two_ne_zero_zmod (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  have hnd : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
  exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr hnd

end Idempotent
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

end ExtCitation.Cyclotomic
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

namespace ExtCitation
namespace Cyclotomic
p2m_export "ExtCitation.Cyclotomic" "thaine_relation_plusField omegaIdempotent_two_cycloUnitTwo_ne_zero unitsEnd unitsEnd_proj unitsEndHom unitsGalAction omegaIdempotent"
p2m_open "ExtCitation.Cyclotomic ExtCitation"

variable (p : ℕ) [Fact p.Prime]

private theorem map_finsetProd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {α : Type*} (s : Finset α) (I : α → Ideal R) :
    Ideal.map f (∏ i ∈ s, I i) = ∏ i ∈ s, Ideal.map f (I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Ideal.map_mul, ih]

private theorem coeIdeal_finsetProd {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {α : Type*} (s : Finset α) (I : α → Ideal R) :
    ((∏ i ∈ s, I i : Ideal R) : FractionalIdeal R⁰ K) =
      ∏ i ∈ s, ((I i : Ideal R) : FractionalIdeal R⁰ K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, FractionalIdeal.coeIdeal_mul, ih]

private theorem ofMul_finsetProd {M : Type*} [CommMonoid M] {α : Type*} (s : Finset α) (f : α → M) :
    Additive.ofMul (∏ i ∈ s, f i) = ∑ i ∈ s, Additive.ofMul (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ofMul_mul, ih]

omit [Fact p.Prime] in

private theorem nsmul_p_clProj_eq_zero {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [NeZero p] (w : ClGalModule p R) : p • w = 0 := by
  obtain ⟨y, rfl⟩ := clProj_surjective p R w
  rw [← map_nsmul]
  exact (ModP.proj_eq_zero_iff p _).mpr ⟨y, rfl⟩

variable (Kplus : Type*) [Field Kplus] [NumberField Kplus]
  [Algebra Kplus (CyclotomicField p ℚ)]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

private theorem thaine_push
    (Δact : (ZMod p)ˣ →* ((𝓞 Kplus) ≃+* (𝓞 Kplus)))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
    (𝔏 : Ideal (𝓞 Kplus)) (t : ZMod p) (α : Kplus) (hα : α ≠ 0) (J₀ : Ideal (𝓞 Kplus))
    (hthaine : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 Kplus)) α =
      (∏ d : (ZMod p)ˣ, (𝔏.map (Δact d).toRingHom :
        FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^
          (t * ((d : ZMod p) ^ 2)⁻¹).val) *
      (J₀ : FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^ p)
    (hmem : Ideal.map (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))) 𝔏 ∈
      (Ideal (𝓞 (CyclotomicField p ℚ)))⁰) :
    ∑ d : (ZMod p)ˣ, (t * ((d : ZMod p) ^ 2)⁻¹).val •
      clGalAction p (CyclotomicField p ℚ) d
        (clProj p (𝓞 (CyclotomicField p ℚ)) (Additive.ofMul (ClassGroup.mk0
          (⟨Ideal.map (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))) 𝔏, hmem⟩ :
            (Ideal (𝓞 (CyclotomicField p ℚ)))⁰)))) = 0 := by
  have hp : p.Prime := Fact.out
  classical

  set ι : (𝓞 Kplus) →+* (𝓞 (CyclotomicField p ℚ)) :=
    algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ)) with hι
  set n : (ZMod p)ˣ → ℕ := fun d => (t * ((d : ZMod p) ^ 2)⁻¹).val with hn
  have hιinj : Function.Injective ι := by
    rw [hι, RingHom.injective_iff_ker_eq_bot]
    exact NumberField.RingOfIntegers.ker_algebraMap_eq_bot Kplus (CyclotomicField p ℚ)

  set W : Ideal (𝓞 Kplus) := (∏ d : (ZMod p)ˣ, (𝔏.map (Δact d).toRingHom) ^ n d) * J₀ ^ p
    with hWdef
  have hWcoe : ((W : Ideal (𝓞 Kplus)) : FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) =
      (∏ d : (ZMod p)ˣ, (𝔏.map (Δact d).toRingHom :
        FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^ n d) *
      (J₀ : FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^ p := by
    rw [hWdef, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow,
      coeIdeal_finsetProd]
    congr 1
    refine Finset.prod_congr rfl fun d _ => ?_
    rw [FractionalIdeal.coeIdeal_pow]
  have hthaine' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 Kplus)) α =
      ((W : Ideal (𝓞 Kplus)) : FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) := by
    rw [hWcoe]; exact hthaine

  have hαmem : α ∈ ((W : Ideal (𝓞 Kplus)) :
      FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) := by
    rw [← hthaine']
    exact FractionalIdeal.mem_spanSingleton_self _ α
  obtain ⟨a₀, ha₀W, ha₀⟩ := (FractionalIdeal.mem_coeIdeal _).mp hαmem
  have hspan : Ideal.span {a₀} = W := by
    have hcoe2 : ((Ideal.span {a₀} : Ideal (𝓞 Kplus)) :
        FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) =
        ((W : Ideal (𝓞 Kplus)) : FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) := by
      rw [FractionalIdeal.coeIdeal_span_singleton, ha₀, hthaine']
    exact (FractionalIdeal.coeIdeal_inj' (le_refl (nonZeroDivisors (𝓞 Kplus)))).mp hcoe2
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    exact hα (by rw [← ha₀, map_zero])

  have hfactor : ∀ d : (ZMod p)ˣ, (𝔏.map (Δact d).toRingHom).map ι =
      (𝔏.map ι).map ((clRingAction p (CyclotomicField p ℚ) d :
        (𝓞 (CyclotomicField p ℚ)) →+* (𝓞 (CyclotomicField p ℚ)))) := by
    intro d
    rw [Ideal.map_map, Ideal.map_map, hΔact d, RingEquiv.toRingHom_eq_coe]
  have hpush : Ideal.span {ι a₀} =
      (∏ d : (ZMod p)ˣ, ((𝔏.map ι).map ((clRingAction p (CyclotomicField p ℚ) d :
        (𝓞 (CyclotomicField p ℚ)) →+* (𝓞 (CyclotomicField p ℚ))))) ^ n d) *
        (J₀.map ι) ^ p := by
    have := congrArg (Ideal.map ι) hspan
    rw [Ideal.map_span, Set.image_singleton] at this
    rw [this, hWdef, Ideal.map_mul, Ideal.map_pow, map_finsetProd]
    congr 1
    refine Finset.prod_congr rfl fun d _ => ?_
    rw [Ideal.map_pow, hfactor d]

  have hJ₀0 : J₀ ≠ ⊥ := by
    rintro rfl
    apply hα
    rw [FractionalIdeal.coeIdeal_bot, zero_pow hp.ne_zero, mul_zero] at hthaine
    exact FractionalIdeal.spanSingleton_eq_zero_iff.mp hthaine
  have hJinfmem : J₀.map ι ∈ (Ideal (𝓞 (CyclotomicField p ℚ)))⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submodule.zero_eq_bot,
      Ideal.map_eq_bot_iff_of_injective hιinj]
    exact hJ₀0
  have hspanmem : Ideal.span {ι a₀} ∈ (Ideal (𝓞 (CyclotomicField p ℚ)))⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submodule.zero_eq_bot,
      Ideal.span_singleton_eq_bot]
    exact fun h => ha₀0 (hιinj (by rw [h, map_zero]))

  set P0 : (Ideal (𝓞 (CyclotomicField p ℚ)))⁰ := ⟨Ideal.map ι 𝔏, hmem⟩ with hP0
  set Q : (ZMod p)ˣ → (Ideal (𝓞 (CyclotomicField p ℚ)))⁰ :=
    fun d => Ideal.mapNonZero (clRingAction p (CyclotomicField p ℚ) d) P0 with hQ
  set Jinf : (Ideal (𝓞 (CyclotomicField p ℚ)))⁰ := ⟨J₀.map ι, hJinfmem⟩ with hJinf

  have hsub : (⟨Ideal.span {ι a₀}, hspanmem⟩ : (Ideal (𝓞 (CyclotomicField p ℚ)))⁰) =
      (∏ d : (ZMod p)ˣ, (Q d) ^ n d) * Jinf ^ p := by
    apply Subtype.ext
    simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, Submonoid.coe_finsetProd,
      hQ, Ideal.coe_mapNonZero, hP0, hJinf]
    exact hpush

  have hone : ClassGroup.mk0 (⟨Ideal.span {ι a₀}, hspanmem⟩ :
      (Ideal (𝓞 (CyclotomicField p ℚ)))⁰) = 1 := by
    rw [ClassGroup.mk0_eq_one_iff]
    exact ⟨⟨ι a₀, rfl⟩⟩
  have hrel : (1 : ClassGroup (𝓞 (CyclotomicField p ℚ))) =
      (∏ d : (ZMod p)ˣ, (ClassGroup.mk0 (Q d)) ^ n d) * (ClassGroup.mk0 Jinf) ^ p := by
    rw [← hone, hsub,
      map_mul (M := (Ideal (𝓞 (CyclotomicField p ℚ)))⁰)
        (N := ClassGroup (𝓞 (CyclotomicField p ℚ))) ClassGroup.mk0,
      map_pow (G := (Ideal (𝓞 (CyclotomicField p ℚ)))⁰)
        (H := ClassGroup (𝓞 (CyclotomicField p ℚ))) ClassGroup.mk0,
      map_prod (M := (Ideal (𝓞 (CyclotomicField p ℚ)))⁰)
        (N := ClassGroup (𝓞 (CyclotomicField p ℚ))) ClassGroup.mk0]
    congr 1
    exact Finset.prod_congr rfl fun d _ =>
      map_pow (G := (Ideal (𝓞 (CyclotomicField p ℚ)))⁰)
        (H := ClassGroup (𝓞 (CyclotomicField p ℚ))) ClassGroup.mk0 (Q d) (n d)

  have hterm : ∀ d : (ZMod p)ˣ,
      (n d) • clGalAction p (CyclotomicField p ℚ) d
        (clProj p (𝓞 (CyclotomicField p ℚ)) (Additive.ofMul (ClassGroup.mk0 P0))) =
      clProj p (𝓞 (CyclotomicField p ℚ))
        (Additive.ofMul ((ClassGroup.mk0 (Q d)) ^ n d)) := by
    intro d
    rw [clGalAction_clProj_mk0, ofMul_pow, map_nsmul]
  calc ∑ d : (ZMod p)ˣ, (n d) • clGalAction p (CyclotomicField p ℚ) d
        (clProj p (𝓞 (CyclotomicField p ℚ)) (Additive.ofMul (ClassGroup.mk0 P0)))
      = ∑ d : (ZMod p)ˣ, clProj p (𝓞 (CyclotomicField p ℚ))
          (Additive.ofMul ((ClassGroup.mk0 (Q d)) ^ n d)) :=
        Finset.sum_congr rfl fun d _ => hterm d
    _ = clProj p (𝓞 (CyclotomicField p ℚ))
          (Additive.ofMul (∏ d : (ZMod p)ˣ, (ClassGroup.mk0 (Q d)) ^ n d)) := by
        rw [ofMul_finsetProd, map_sum]
    _ = clProj p (𝓞 (CyclotomicField p ℚ))
          (Additive.ofMul (((ClassGroup.mk0 Jinf)⁻¹) ^ p)) := by
        congr 1
        have h := hrel
        rw [eq_comm, mul_comm, ← eq_inv_mul_iff_mul_eq, mul_one] at h
        rw [h, inv_pow]
    _ = p • clProj p (𝓞 (CyclotomicField p ℚ))
          (Additive.ofMul ((ClassGroup.mk0 Jinf)⁻¹)) := by
        rw [ofMul_pow, map_nsmul]
    _ = 0 := nsmul_p_clProj_eq_zero p _

end ExtCitation.Cyclotomic
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

section Solution

p2m_open "ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic Ideal NumberField.Ideal"

variable (p : ℕ) [hp : Fact p.Prime]

local notation3 "K" => CyclotomicField p ℚ
local notation3 "Kplus" => ↥(NumberField.maximalRealSubfield (CyclotomicField p ℚ))

private noncomputable def e₂clProj : Additive (ClassGroup (𝓞 K)) →+ ClGalModule p (𝓞 K) :=
  (omegaIdempotent p (clGalAction p K) 2).toAddMonoidHom.comp (clProj p (𝓞 K))

private lemma e₂clProj_ofMul (C : ClassGroup (𝓞 K)) :
    e₂clProj p (Additive.ofMul C) =
      omegaIdempotent p (clGalAction p K) 2 (clProj p (𝓞 K) (Additive.ofMul C)) := rfl

theorem solution (hp5 : 5 ≤ p) :
    ∀ a : ClGalModule p (𝓞 (CyclotomicField p ℚ)),
      IsOmegaEigenvector (clGalAction p (CyclotomicField p ℚ)) 2 a →
        a = 0 := by
  intro a ha
  haveI hCM : IsCMField K := isCMField_cyclo p hp5

  obtain ⟨δ, hδeig, hδpow⟩ := delta_package p hp5 Kplus (ΔactE2 p) (ΔactE2_spec p)
    (exists_real_unit_of_conj_fixed p)
  set aδ : 𝓞 K := algebraMap (𝓞 Kplus) (𝓞 K) (δ : 𝓞 Kplus) with haδ
  have haδu : IsUnit aδ := ⟨Units.map (algebraMap (𝓞 Kplus) (𝓞 K) : 𝓞 Kplus →* 𝓞 K) δ, rfl⟩

  haveI hGalM : IsGalois K (KumField p (aδ : K)) := isGalois_kumField p hδpow
  have hdegM : Module.finrank K (KumField p (aδ : K)) = p := finrank_kumField p hδpow

  have hNSG := NumberField.classGroup_eq_closure_nonSplit_degOne K (KumField p (aδ : K)) p
    hp.out (by omega) hdegM

  obtain ⟨C, rfl⟩ := clProj_surjective p (𝓞 K) a
  rw [← omegaIdempotent_apply_of_isOmegaEigenvector p (clGalAction p K) 2 _ ha]
  change e₂clProj p (Additive.ofMul (Additive.toMul C)) = 0
  refine addHom_eq_zero_of_closure_eq_top (e₂clProj p) _ hNSG ?_ (Additive.toMul C)

  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  obtain ⟨𝔓, hmax, hℓprime, hns, rfl⟩ := hc
  rw [e₂clProj_ofMul]
  set ℓ := Ideal.absNorm (𝔓 : Ideal (𝓞 K)) with hℓdef
  rcases eq_or_ne ℓ p with hℓp | hℓp
  ·
    rw [mk0_eq_one_of_absNorm_eq_p p 𝔓 hmax hℓp]
    simp only [ofMul_one, map_zero]
  ·
    set 𝔏 := Ideal.relNorm (𝓞 Kplus) (𝔓 : Ideal (𝓞 K)) with h𝔏def
    have h𝔏max : 𝔏.IsMaximal := relNorm_P_isMaximal p hℓprime (𝔓 : Ideal (𝓞 K)) rfl
    have h𝔏deg : Ideal.absNorm 𝔏 = ℓ := absNorm_relNorm_P p (𝔓 : Ideal (𝓞 K))
    have h𝔏0 : 𝔏 ≠ ⊥ := fun h => hℓprime.ne_zero (by
      have : Ideal.absNorm 𝔏 = 0 := by rw [h, Ideal.absNorm_bot]
      rw [h𝔏deg] at this
      exact this)

    have hPres : ∀ y : 𝓞 K, aδ - y ^ p ∉ (𝔓 : Ideal (𝓞 K)) :=
      not_pow_residue_of_not_isSplitPrime p aδ hδpow (𝔓 : Ideal (𝓞 K)) hmax
        hℓprime hℓp rfl haδu hns
    have hle : 𝔏 ≤ (𝔓 : Ideal (𝓞 K)).comap (algebraMap (𝓞 Kplus) (𝓞 K)) :=
      Ideal.relNorm_le_comap (𝓞 Kplus) (𝔓 : Ideal (𝓞 K))
    have hδ𝔏 := mk_not_mem_pow_of_map (algebraMap (𝓞 Kplus) (𝓞 K)) 𝔏 (𝔓 : Ideal (𝓞 K))
      hle (δ : 𝓞 Kplus) p hPres

    obtain ⟨α, hα, t, ht, J₀, hthaine⟩ := thaine_relation_plusField p hp5
      Kplus (finrank_maximalRealSubfield p) (ΔactE2 p) (ΔactE2_spec p)
      ℓ hℓprime hℓp 𝔏 h𝔏max h𝔏deg δ hδeig hδ𝔏

    have h𝔓0 : (𝔓 : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero 𝔓
    have hJ𝔓0 : (𝔓 : Ideal (𝓞 K)).map (clRingAction p K (-1)) ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective (clRingAction p K (-1)).injective]
      exact h𝔓0
    have h𝔏K0 : 𝔏.map (algebraMap (𝓞 Kplus) (𝓞 K)) ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
      rw [mem_nonZeroDivisors_iff_ne_zero, map_relNorm_P p (𝔓 : Ideal (𝓞 K))]
      exact mul_ne_zero h𝔓0 hJ𝔓0

    have hpush := thaine_push p Kplus (ΔactE2 p) (ΔactE2_spec p) 𝔏 t α hα J₀ hthaine h𝔏K0

    set x := clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0 𝔓)) with hxdef
    have hsplit :
        clProj p (𝓞 K) (Additive.ofMul
          (ClassGroup.mk0 ⟨𝔏.map (algebraMap (𝓞 Kplus) (𝓞 K)), h𝔏K0⟩)) =
        x + clGalAction p K (-1) x := by
      have hsubmul :
          (⟨𝔏.map (algebraMap (𝓞 Kplus) (𝓞 K)), h𝔏K0⟩ : (Ideal (𝓞 K))⁰) =
            𝔓 * (Ideal.mapNonZero (clRingAction p K (-1)) 𝔓) := by
        refine Subtype.ext ?_
        simp only [Submonoid.coe_mul, Ideal.coe_mapNonZero]
        exact map_relNorm_P p (𝔓 : Ideal (𝓞 K))
      rw [hsubmul, MonoidHom.map_mul, ofMul_mul, map_add, hxdef, clGalAction_clProj_mk0]
    rw [hsplit] at hpush

    have hpush' :
        ∑ d : (ZMod p)ˣ, (t * ((d : ZMod p) ^ 2)⁻¹) •
          clGalAction p K d (x + clGalAction p K (-1) x) = 0 := by
      rw [← hpush]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [val_nsmul_eq]
    rw [sum_tinv_smul_eq p (clGalAction p K) 2 t] at hpush'

    have h2e : omegaIdempotent p (clGalAction p K) 2 (x + clGalAction p K (-1) x) =
        (2 : ZMod p) • omegaIdempotent p (clGalAction p K) 2 x := by
      rw [map_add, omegaIdempotent_act, act_omegaIdempotent, Units.val_neg, Units.val_one,
        neg_one_sq, one_smul, two_smul]
    rw [h2e, smul_smul] at hpush'
    have hnz : (-t) * (2 : ZMod p) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr ht) (two_ne_zero_zmod p hp5)
    exact (smul_eq_zero.mp hpush').resolve_left hnz

end Solution
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.ExtCitation.Cyclotomic"

end S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot
end P2MW
export P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot (solution)
