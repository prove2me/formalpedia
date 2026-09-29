-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_ringHom_ker_residue_comp_eq_ker_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0b861468-cef6-57f1-9953-6ea506931138

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot
import Theorems.Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_ker_residue_comp_eq_ker_of_one_le

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace LiftDVRCore

open IsLocalRing TensorProduct

theorem finite_of_module_finite_int_of_charP (B : Type) [CommRing B] [Module.Finite ℤ B] (p : ℕ) [Fact p.Prime]
    [CharP B p] : Finite B := by
  letI : Algebra (ZMod p) B := ZMod.algebra B p
  haveI : Module.Finite (ZMod p) B := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) B
  exact Module.finite_of_finite (ZMod p)

theorem stageAB (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A]
    [Module.IsTorsionFree ℤ_[p] A] (I : Ideal A) [hImax : I.IsMaximal] :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪') (_ : Algebra ℤ_[p] 𝒪')
      (_ : IsLocalHom (algebraMap ℤ_[p] 𝒪')),
      ∃ χ : A →+* 𝒪', ∀ a ∈ I, χ a ∈ IsLocalRing.maximalIdeal 𝒪' := by
  classical
  haveI : Finite (IsLocalRing.ResidueField ℤ_[p]) := Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  obtain ⟨hfinmax, hbij, hfinI, -⟩ :=
    Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite (𝒪 := ℤ_[p]) A
  haveI : Module.Finite ℤ_[p] (Localization.AtPrime I) := hfinI ⟨I, hImax⟩

  let Φ : A ≃+* (∀ J : MaximalSpectrum A, Localization.AtPrime J.asIdeal) := RingEquiv.ofBijective _ hbij
  have hΦsmul : ∀ (r : ℤ_[p]) (a : A), Φ (r • a) = r • Φ a := by
    intro r a
    funext J
    show algebraMap A (Localization.AtPrime J.asIdeal) (r • a) = r • algebraMap A (Localization.AtPrime J.asIdeal) a
    rw [Algebra.smul_def r a, map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] A (Localization.AtPrime J.asIdeal)]
  let gP : Localization.AtPrime I → A := fun x => Φ.symm (Pi.single (⟨I, hImax⟩ : MaximalSpectrum A) x)
  have hgP_inj : Function.Injective gP := by
    intro x y h
    have := congrArg Φ h
    simp only [gP, RingEquiv.apply_symm_apply] at this
    exact Pi.single_injective (M := fun J : MaximalSpectrum A => Localization.AtPrime J.asIdeal) _ this
  have hgP_smul : ∀ (r : ℤ_[p]) (x : Localization.AtPrime I), gP (r • x) = r • gP x := by
    intro r x
    apply Φ.injective
    simp only [gP, RingEquiv.apply_symm_apply, hΦsmul]
    rw [Pi.single_smul]
  haveI : Module.IsTorsionFree ℤ_[p] (Localization.AtPrime I) := hgP_inj.moduleIsTorsionFree gP hgP_smul

  set Nl : Ideal (Localization.AtPrime I) := nilradical (Localization.AtPrime I) with hNl
  have hniltop : Nl ≠ ⊤ := by
    intro h
    have : (1 : Localization.AtPrime I) ∈ Nl := h ▸ Submodule.mem_top
    obtain ⟨n, hn⟩ := mem_nilradical.mp this
    exact one_ne_zero (by rwa [one_pow] at hn)
  haveI : Nontrivial (Localization.AtPrime I ⧸ Nl) := Ideal.Quotient.nontrivial_iff.mpr hniltop
  haveI : IsLocalRing (Localization.AtPrime I ⧸ Nl) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Nl) Ideal.Quotient.mk_surjective
  haveI : IsReduced (Localization.AtPrime I ⧸ Nl) := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  haveI : Module.Finite ℤ_[p] (Localization.AtPrime I ⧸ Nl) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] Nl).toLinearMap (Ideal.Quotient.mkₐ_surjective ℤ_[p] Nl)
  haveI : Module.IsTorsionFree ℤ_[p] (Localization.AtPrime I ⧸ Nl) := by
    refine Module.IsTorsionFree.of_smul_eq_zero (fun r x h => ?_)
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      have h' : Ideal.Quotient.mk Nl (r • x) = 0 := by
        rw [← h, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
      rw [Ideal.Quotient.eq_zero_iff_mem] at h' ⊢
      obtain ⟨n, hn⟩ := mem_nilradical.mp h'
      rw [smul_pow] at hn
      have hrn : r ^ n ≠ 0 := pow_ne_zero n hr
      have hxn : x ^ n = 0 := by
        rcases smul_eq_zero.mp hn with h1 | h2
        · exact absurd h1 hrn
        · exact h2
      exact mem_nilradical.mpr ⟨n, hxn⟩

  haveI hmkloc : IsLocalHom (Ideal.Quotient.mk Nl) := by
    apply isLocalHom_of_le_jacobson_bot
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hniltop

  obtain ⟨n, Ai, i1, i2, i3, i4, i5, i6, i7, i8, i9, χ, hloc, hinf, -⟩ :=
    IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot (𝒪 := ℤ_[p]) (P := Localization.AtPrime I ⧸ Nl)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      haveI : IsEmpty (Fin 0) := inferInstance
      rw [iInf_of_empty] at hinf
      exact bot_ne_top hinf.symm
    · exact h
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨Ai i₀, i1 i₀, i2 i₀, i3 i₀, i4 i₀, i5 i₀, i6 i₀, i7 i₀, i9 i₀,
    (χ i₀).toRingHom.comp ((Ideal.Quotient.mk Nl).comp (algebraMap A (Localization.AtPrime I))), ?_⟩
  intro a ha

  have h1 : algebraMap A (Localization.AtPrime I) a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime I) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime I) I a).mpr ha
  have h2 : Ideal.Quotient.mk Nl (algebraMap A (Localization.AtPrime I) a) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime I ⧸ Nl) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun hu => h1 (IsUnit.of_map _ _ hu)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2 ⊢
  intro hu
  exact h2 ((hloc i₀).map_nonunit _ hu)

theorem core {T : Type} [CommRing T] [Module.Finite ℤ T] [Module.IsTorsionFree ℤ T]
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p] (θ : T →+* F) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪'),
      (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪' ∧
      ∃ χ : T →+* 𝒪', RingHom.ker ((IsLocalRing.residue 𝒪').comp χ) = RingHom.ker θ := by
  classical

  haveI h𝔪p : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime θ
  haveI : CharP (T ⧸ RingHom.ker θ) p := by
    have hinj : Function.Injective (Ideal.Quotient.lift (RingHom.ker θ) θ (fun a ha => ha)) := RingHom.kerLift_injective θ
    exact (RingHom.charP_iff _ hinj p).mpr inferInstance
  haveI : Module.Finite ℤ (T ⧸ RingHom.ker θ) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ (RingHom.ker θ)).toLinearMap (Ideal.Quotient.mkₐ_surjective ℤ (RingHom.ker θ))
  haveI : Finite (T ⧸ RingHom.ker θ) := finite_of_module_finite_int_of_charP (T ⧸ RingHom.ker θ) p
  haveI h𝔪max : (RingHom.ker θ).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isDomain_to_isField (T ⧸ RingHom.ker θ))

  haveI : Module.Free ℤ T := Module.free_of_finite_type_torsion_free'
  haveI : Module.IsTorsionFree ℤ_[p] (ℤ_[p] ⊗[ℤ] T) :=
    Module.IsTorsionFree.of_smul_eq_zero (fun r m h => (smul_eq_zero.mp h))

  let castF : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  let f₁ : ℤ_[p] →ₐ[ℤ] F := (castF.comp (PadicInt.toZMod (p := p))).toIntAlgHom
  let fA : ℤ_[p] ⊗[ℤ] T →ₐ[ℤ] F := Algebra.TensorProduct.lift f₁ θ.toIntAlgHom (fun x y => Commute.all _ _)
  have hfA_tmul : ∀ (a : ℤ_[p]) (t : T), fA (a ⊗ₜ t) = f₁ a * θ t := fun a t => Algebra.TensorProduct.lift_tmul _ _ _ a t
  have hrange : ∀ x : ℤ_[p] ⊗[ℤ] T, fA x ∈ θ.range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a t =>
      rw [hfA_tmul]
      refine mul_mem ?_ ⟨t, rfl⟩
      show castF (PadicInt.toZMod a) ∈ θ.range
      have : castF (PadicInt.toZMod a) = ((PadicInt.toZMod a).val : F) := by
        rw [← map_natCast castF, ZMod.natCast_zmod_val]
      rw [this]
      exact natCast_mem _ _
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  haveI hIp : (RingHom.ker fA.toRingHom).IsPrime := RingHom.ker_isPrime _
  haveI : Finite (ℤ_[p] ⊗[ℤ] T ⧸ RingHom.ker fA.toRingHom) := by
    haveI : Finite θ.range := Finite.of_equiv _ (RingHom.quotientKerEquivRange θ).toEquiv
    have hr' : ∀ x : fA.toRingHom.range, (x : F) ∈ θ.range := by
      rintro ⟨_, y, rfl⟩; exact hrange y
    haveI : Finite fA.toRingHom.range :=
      Finite.of_injective (fun x : fA.toRingHom.range => (⟨x.1, hr' x⟩ : θ.range))
        (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
    exact Finite.of_equiv _ (RingHom.quotientKerEquivRange fA.toRingHom).symm.toEquiv
  haveI hImax : (RingHom.ker fA.toRingHom).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isDomain_to_isField (ℤ_[p] ⊗[ℤ] T ⧸ RingHom.ker fA.toRingHom))

  obtain ⟨𝒪', j1, j2, j3, j4, j5, j6, j7, j8, χA, hχA⟩ := stageAB p (ℤ_[p] ⊗[ℤ] T) (RingHom.ker fA.toRingHom)
  refine ⟨𝒪', j1, j2, j3, j4, j5, j6, ?_, χA.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := T)).toRingHom, ?_⟩
  ·
    have hp : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hp ⊢
    rw [← map_natCast (algebraMap ℤ_[p] 𝒪') p]
    exact fun h => hp ((isUnit_map_iff (algebraMap ℤ_[p] 𝒪') _).1 h)
  ·
    apply le_antisymm
    ·
      intro t ht
      by_contra hnot

      have hle : RingHom.ker θ ≤ RingHom.ker ((IsLocalRing.residue 𝒪').comp (χA.comp
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := T)).toRingHom)) := by
        intro s hs
        rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
        apply hχA
        rw [RingHom.mem_ker]
        show fA ((1 : ℤ_[p]) ⊗ₜ s) = 0
        rw [hfA_tmul, RingHom.mem_ker.mp hs, mul_zero]
      have hne : RingHom.ker ((IsLocalRing.residue 𝒪').comp (χA.comp
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := T)).toRingHom)) ≠ ⊤ :=
        RingHom.ker_ne_top _
      have heq := h𝔪max.eq_of_le hne hle
      exact hnot (heq ▸ ht)
    · intro s hs
      rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
      apply hχA
      rw [RingHom.mem_ker]
      show fA ((1 : ℤ_[p]) ⊗ₜ s) = 0
      rw [hfA_tmul, RingHom.mem_ker.mp hs, mul_zero]

end LiftDVRCore

theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 1 ≤ k) (S : Set ℕ) (hint : CuspForm.HasIntegralStructure N k)
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (θ : CuspForm.heckeAlgebra N k S →+* F) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪'),
      (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪' ∧
      ∃ χ : CuspForm.heckeAlgebra N k S →+* 𝒪',
        RingHom.ker ((IsLocalRing.residue 𝒪').comp χ) = RingHom.ker θ := by
  haveI : Module.Finite ℤ (CuspForm.heckeAlgebra N k S) := hint.moduleFinite_heckeAlgebra hk S

  haveI : Module.IsTorsionFree ℤ (CuspForm.heckeAlgebra N k S) := by
    rw [Module.isTorsionFree_int_iff_isAddTorsionFree]
    infer_instance
  exact LiftDVRCore.core p θ

end S_CuspForm_heckeAlgebra_exists_ringHom_ker_residue_comp_eq_ker_of_one_le
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_ker_residue_comp_eq_ker_of_one_le (solution)
