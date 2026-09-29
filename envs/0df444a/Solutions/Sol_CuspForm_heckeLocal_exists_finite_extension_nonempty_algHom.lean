-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_finite_extension_nonempty_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c74b980d-6906-5ee7-bf4f-949b8fa99aa9

import Mathlib
import Definitions.Def_CuspForm_HeckeLocal
import Theorems.Thm_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_finite_extension_nonempty_algHom

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace PointAux

open IsLocalRing

theorem exists_local_point {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T] :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪')
      (_ : Finite (ResidueField 𝒪')) (_ : CharZero 𝒪') (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪')
      (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
      ∃ χ : T →ₐ[𝒪] 𝒪', IsLocalHom χ.toRingHom := by
  classical
  haveI : Module.IsTorsionFree 𝒪 T := Module.IsTorsionFree.of_smul_eq_zero (fun r m h => smul_eq_zero.mp h)
  set Nl : Ideal T := nilradical T with hNl
  have hniltop : Nl ≠ ⊤ := by
    intro h
    have : (1 : T) ∈ Nl := h ▸ Submodule.mem_top
    obtain ⟨n, hn⟩ := mem_nilradical.mp this
    exact one_ne_zero (by rwa [one_pow] at hn)
  haveI : Nontrivial (T ⧸ Nl) := Ideal.Quotient.nontrivial_iff.mpr hniltop
  haveI : IsLocalRing (T ⧸ Nl) := IsLocalRing.of_surjective' (Ideal.Quotient.mk Nl) Ideal.Quotient.mk_surjective
  haveI : IsReduced (T ⧸ Nl) := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  haveI : Module.Finite 𝒪 (T ⧸ Nl) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 Nl).toLinearMap (Ideal.Quotient.mkₐ_surjective 𝒪 Nl)
  haveI : Module.IsTorsionFree 𝒪 (T ⧸ Nl) := by
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
      have hxn : x ^ n = 0 := by
        rcases smul_eq_zero.mp hn with h1 | h2
        · exact absurd h1 (pow_ne_zero n hr)
        · exact h2
      exact mem_nilradical.mpr ⟨n, hxn⟩
  haveI hmkloc : IsLocalHom (Ideal.Quotient.mk Nl) := by
    apply isLocalHom_of_le_jacobson_bot
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hniltop
  obtain ⟨n, Ai, i1, i2, i3, i4, i5, i6, i7, i8, i9, χ, hloc, hinf, -⟩ :=
    IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot (𝒪 := 𝒪) (P := T ⧸ Nl)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      rw [iInf_of_empty] at hinf
      exact bot_ne_top hinf.symm
    · exact h
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨Ai i₀, i1 i₀, i2 i₀, i3 i₀, i4 i₀, i5 i₀, i6 i₀, i7 i₀, i8 i₀, i9 i₀, (χ i₀).comp (Ideal.Quotient.mkₐ 𝒪 Nl), ?_⟩
  show IsLocalHom ((χ i₀).toRingHom.comp (Ideal.Quotient.mk Nl))
  haveI := hloc i₀
  exact RingHom.isLocalHom_comp _ _

theorem algebraMap_injective_of_charZero {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Finite (ResidueField 𝒪)] (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra 𝒪 A] :
    Function.Injective (algebraMap 𝒪 A) := by
  rw [injective_iff_map_eq_zero]
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha0, hane⟩ := hcon
  have hker : RingHom.ker (algebraMap 𝒪 A) ≠ ⊥ := by
    intro h; exact hane ((RingHom.mem_ker).mpr ha0 |> (h ▸ ·) |> (Ideal.mem_bot).mp)
  haveI : (RingHom.ker (algebraMap 𝒪 A)).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (algebraMap 𝒪 A)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hker
  have heq : RingHom.ker (algebraMap 𝒪 A) = maximalIdeal 𝒪 := IsLocalRing.eq_maximalIdeal hmax

  letI : Fintype (ResidueField 𝒪) := Fintype.ofFinite _
  obtain ⟨ℓ, hℓ⟩ := CharP.exists (ResidueField 𝒪)
  haveI := hℓ
  have hℓprime : ℓ.Prime := (CharP.char_is_prime_or_zero (ResidueField 𝒪) ℓ).resolve_right (CharP.char_ne_zero_of_finite (ResidueField 𝒪) ℓ)
  have hℓmem : (ℓ : 𝒪) ∈ maximalIdeal 𝒪 := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ ℓ
  rw [← heq, RingHom.mem_ker, map_natCast] at hℓmem
  exact hℓprime.ne_zero (Nat.cast_eq_zero.mp hℓmem)

end PointAux

theorem solution
    (N : ℕ) [NeZero N] (S : Finset ℕ)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    Nonempty (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪'
        ((IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪')).comp θ) →ₐ[𝒪'] 𝒪') := by
  classical

  obtain ⟨𝒪', j1, j2, j3, j4, j5, j6, j7, j8, j9, χ₀, hχ₀⟩ :=
    PointAux.exists_local_point (𝒪 := 𝒪) (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)
  haveI := hχ₀
  have hinj : Function.Injective (algebraMap 𝒪 𝒪') := PointAux.algebraMap_injective_of_charZero (𝒪 := 𝒪) 𝒪'
  refine ⟨𝒪', j1, j2, j3, j4, j5, j6, j7, j8, j9, hinj, ?_⟩

  let g : ↥(CuspForm.heckeLatticeAlgebra N (↑S : Set ℕ)) →+* 𝒪' :=
    χ₀.toRingHom.comp ((algebraMap (CuspForm.heckeBaseAlgebra N (↑S : Set ℕ) 𝒪) (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)).comp
      (Algebra.TensorProduct.includeRight.toRingHom :
        ↥(CuspForm.heckeLatticeAlgebra N (↑S : Set ℕ)) →+* CuspForm.heckeBaseAlgebra N (↑S : Set ℕ) 𝒪))
  have hgπ : ∀ t, g (CuspForm.latticeRestrictHom N (↑S : Set ℕ) t) = χ₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ t) :=
    fun t => rfl

  have hkey : ∀ t, IsLocalRing.residue 𝒪' (g (CuspForm.latticeRestrictHom N (↑S : Set ℕ) t))
      = IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') (θ t) := by
    intro t
    rw [hgπ]
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (θ t)
    have h1 : IsLocalRing.residue _ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ t)
        = IsLocalRing.residue _ (algebraMap 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) a) := by
      rw [CuspForm.heckeLocal.residue_pi, ← ha, IsLocalRing.ResidueField.map_residue]
    have h2 : CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ t - algebraMap 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) a
        ∈ IsLocalRing.maximalIdeal (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h1, sub_self]
    have h3 : χ₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ t - algebraMap 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) a)
        ∈ IsLocalRing.maximalIdeal 𝒪' := map_nonunit χ₀.toRingHom _ h2
    rw [map_sub, AlgHom.commutes, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h3
    rw [h3, ← ha, IsLocalRing.ResidueField.map_residue]

  let f : CuspForm.heckeBaseAlgebra N (↑S : Set ℕ) 𝒪' →+* 𝒪' :=
    (Algebra.TensorProduct.lift (AlgHom.id ℤ 𝒪') g.toIntAlgHom (fun _ _ => Commute.all _ _)).toRingHom
  have hf_tmul : ∀ (a : 𝒪') (s : ↥(CuspForm.heckeLatticeAlgebra N (↑S : Set ℕ))),
      f ((a ⊗ₜ[ℤ] s : 𝒪' ⊗[ℤ] ↥(CuspForm.heckeLatticeAlgebra N (↑S : Set ℕ)))) = a * g s :=
    fun a s => Algebra.TensorProduct.lift_tmul _ _ _ a s

  have hcompat : ∀ y : 𝒪' ⊗[ℤ] ↥(CuspForm.heckeAlgebra N 2 (↑S : Set ℕ)),
      IsLocalRing.residue 𝒪' (f (CuspForm.latticeBaseChange N (↑S : Set ℕ) 𝒪' y))
        = CuspForm.residualCharacter N (↑S : Set ℕ) 𝒪' ((IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪')).comp θ) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a t =>
      rw [CuspForm.latticeBaseChange_tmul, CuspForm.residualCharacter_tmul, hf_tmul, map_mul, hkey]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

  have hunit : ∀ s : ↥(CuspForm.heckeLocalSubmonoid N (↑S : Set ℕ) 𝒪' ((IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪')).comp θ)),
      IsUnit (f s) := by
    intro s
    by_contra hns
    have hsJ : f s ∈ IsLocalRing.maximalIdeal 𝒪' := hns
    set J : Ideal (CuspForm.heckeBaseAlgebra N (↑S : Set ℕ) 𝒪') := RingHom.ker ((IsLocalRing.residue 𝒪').comp f) with hJ
    have hle : CuspForm.heckeLocalIdeal N (↑S : Set ℕ) 𝒪' ((IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪')).comp θ) ≤ J := by
      intro x hx
      rw [CuspForm.heckeLocalIdeal, Ideal.mem_map_iff_of_surjective _ (CuspForm.latticeBaseChange_surjective N (↑S : Set ℕ) 𝒪')] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hJ, RingHom.mem_ker, RingHom.comp_apply, hcompat]
      exact (CuspForm.mem_heckeCharKernel_iff N (↑S : Set ℕ) 𝒪' _ y).mp hy
    have hJne : J ≠ ⊤ := RingHom.ker_ne_top _
    have hJeq := (CuspForm.heckeLocalIdeal.instIsMaximal N (↑S : Set ℕ) 𝒪'
      ((IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪')).comp θ)).eq_of_le hJne hle
    have hs : (s : CuspForm.heckeBaseAlgebra N (↑S : Set ℕ) 𝒪') ∈ J := by
      rw [hJ, RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]; exact hsJ
    rw [← hJeq] at hs
    exact ((CuspForm.mem_heckeLocalSubmonoid_iff N (↑S : Set ℕ) 𝒪' _
      (CuspForm.ker_latticeBaseChange_le_heckeCharKernel N (↑S : Set ℕ) 𝒪' _) s).mp s.2) hs

  let Ψ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪' ((IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪')).comp θ) →+* 𝒪' :=
    IsLocalization.lift (M := CuspForm.heckeLocalSubmonoid N (↑S : Set ℕ) 𝒪' ((IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪')).comp θ)) hunit
  refine ⟨{ Ψ with commutes' := fun a => ?_ }⟩
  show Ψ (algebraMap 𝒪' _ a) = a
  rw [IsScalarTower.algebraMap_apply 𝒪' (CuspForm.heckeBaseAlgebra N (↑S : Set ℕ) 𝒪') _ a, IsLocalization.lift_eq]
  show f ((a ⊗ₜ[ℤ] (1 : ↥(CuspForm.heckeLatticeAlgebra N (↑S : Set ℕ)))) : 𝒪' ⊗[ℤ] ↥(CuspForm.heckeLatticeAlgebra N (↑S : Set ℕ))) = a
  rw [hf_tmul, map_one, mul_one]

end S_CuspForm_heckeLocal_exists_finite_extension_nonempty_algHom
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_finite_extension_nonempty_algHom (solution)
