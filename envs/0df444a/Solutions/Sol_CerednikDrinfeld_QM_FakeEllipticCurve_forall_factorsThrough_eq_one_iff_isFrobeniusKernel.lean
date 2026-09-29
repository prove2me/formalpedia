-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_eq_one_iff_isFrobeniusKernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c8d6bb7b-1003-5a4a-8574-21aeb6dfbc1e

import Mathlib
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
import Theorems.Thm_AlgebraicGeometry_Smooth_isFinite_and_flat_and_surjective_of_isPullback_frobenius
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_finrank_eq_pow_of_isPullback_frobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_eq_one_iff_isFrobeniusKernel
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base RegularLocalRingQuotientAscent.dualNumberFst_apply QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace MoritaAlg

open TensorProduct

theorem conv_sub_add_mem_sq
    {k : Type u} [Field k] {H : Type u} [CommRing H] [Bialgebra k H]
    (φ ψ : H →ₐ[k] H)
    (hφ : ∀ a, Coalgebra.counit (R := k) (φ a) = Coalgebra.counit a)
    (hψ : ∀ a, Coalgebra.counit (R := k) (ψ a) = Coalgebra.counit a)
    (a : H) (ha : Coalgebra.counit (R := k) a = 0) :
    (WithConv.toConv φ * WithConv.toConv ψ).ofConv a - (φ a + ψ a) ∈
      (RingHom.ker (Bialgebra.counitAlgHom k H)) ^ 2 := by
  classical
  set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom k H) with hI
  have memI : ∀ x : H, x ∈ I ↔ Coalgebra.counit (R := k) x = 0 := fun x ↦ by
    simp [hI, RingHom.mem_ker]
  let 𝓡 := Coalgebra.Repr.arbitrary k a

  have key : (WithConv.toConv φ * WithConv.toConv ψ).ofConv a =
      ∑ i ∈ 𝓡.index, φ (𝓡.left i) * ψ (𝓡.right i) := by
    have h1 := congrArg WithConv.ofConv
      (AlgHom.toLinearMap_convMul (WithConv.toConv φ) (WithConv.toConv ψ))
    have h2 := Coalgebra.Repr.convMul_apply 𝓡 (WithConv.toConv φ.toLinearMap)
      (WithConv.toConv ψ.toLinearMap)
    simp only at h1
    rw [← AlgHom.toLinearMap_apply, h1]
    exact h2

  have e1 : ∑ i ∈ 𝓡.index, φ (𝓡.left i) * algebraMap k H (Coalgebra.counit (𝓡.right i)) = φ a := by
    have h := congrArg (TensorProduct.rid k H)
      (Coalgebra.sum_map_tmul_counit_eq (R := k) φ a (repr := 𝓡))
    simp only [map_sum, TensorProduct.rid_tmul, one_smul] at h
    simpa only [Algebra.smul_def, mul_comm] using h
  have e2 : ∑ i ∈ 𝓡.index, algebraMap k H (Coalgebra.counit (𝓡.left i)) * ψ (𝓡.right i) = ψ a := by
    have h := congrArg (TensorProduct.lid k H)
      (Coalgebra.sum_counit_tmul_map_eq (R := k) ψ a (repr := 𝓡))
    simp only [map_sum, TensorProduct.lid_tmul, one_smul] at h
    simpa only [Algebra.smul_def] using h
  have e3 : ∑ i ∈ 𝓡.index, algebraMap k H (Coalgebra.counit (𝓡.left i)) *
      algebraMap k H (Coalgebra.counit (𝓡.right i)) = 0 := by
    have h := congrArg (Coalgebra.counit (R := k) (A := H)) (Coalgebra.sum_counit_smul 𝓡)
    simp only [map_sum, map_smul, smul_eq_mul] at h
    rw [ha] at h
    simp_rw [← map_mul]
    rw [← map_sum, h, map_zero]
  have hcounit_alg : ∀ c : k, Coalgebra.counit (R := k) (algebraMap k H c) = c := fun c ↦ by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one]
  have hu : ∀ i, φ (𝓡.left i) - algebraMap k H (Coalgebra.counit (𝓡.left i)) ∈ I := fun i ↦ by
    rw [memI, map_sub, hφ, hcounit_alg, sub_self]
  have hv : ∀ i, ψ (𝓡.right i) - algebraMap k H (Coalgebra.counit (𝓡.right i)) ∈ I := fun i ↦ by
    rw [memI, map_sub, hψ, hcounit_alg, sub_self]
  have expand : (WithConv.toConv φ * WithConv.toConv ψ).ofConv a - (φ a + ψ a) =
      ∑ i ∈ 𝓡.index, (φ (𝓡.left i) - algebraMap k H (Coalgebra.counit (𝓡.left i))) *
        (ψ (𝓡.right i) - algebraMap k H (Coalgebra.counit (𝓡.right i))) := by
    rw [key]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [e1, e2, e3]
    abel
  rw [expand, pow_two]
  exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_mul (hu i) (hv i)

theorem isLocalRing_of_subsingleton_algHom
    {k : Type u} [Field k] [IsAlgClosed k] {H : Type u} [CommRing H] [Algebra k H] [Module.Finite k H]
    [Nontrivial H] (h : Subsingleton (H →ₐ[k] k)) : IsLocalRing H := by
  have hker : ∀ m : Ideal H, m.IsMaximal → ∃ χ : H →ₐ[k] k, ∀ x, χ x = 0 ↔ x ∈ m := by
    intro m hm
    letI : Field (H ⧸ m) := Ideal.Quotient.field m
    haveI : Module.Finite k (H ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap (Ideal.Quotient.mkₐ_surjective k m)
    haveI : Algebra.IsIntegral k (H ⧸ m) := Algebra.IsIntegral.of_finite k (H ⧸ m)
    have hb : Function.Bijective (Algebra.ofId k (H ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := H ⧸ m)
    let e : k ≃ₐ[k] H ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (H ⧸ m)) hb
    refine ⟨(e.symm : H ⧸ m →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), fun x ↦ ?_⟩
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_algHom,
      map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨m, hm⟩ := Ideal.exists_maximal H
  refine ⟨m, hm, fun m' hm' ↦ ?_⟩
  obtain ⟨χ, hχ⟩ := hker m hm
  obtain ⟨χ', hχ'⟩ := hker m' hm'
  have hχχ : χ' = χ := Subsingleton.elim _ _
  ext x
  rw [← hχ', hχχ, hχ]

theorem two_le_finrank_of_antirep
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {B : Type*} [Ring B] [Algebra ℚ B] (Λ : Submodule ℤ B)
    (h1 : (1 : B) ∈ Λ) (hmulmem : ∀ x y : ↥Λ, (x : B) * (y : B) ∈ Λ)
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p))
    (hφ1 : φ ⟨1, h1⟩ = 1)
    (hφmul : ∀ (x y : ↥Λ), φ ⟨(x : B) * (y : B), hmulmem x y⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : B) = (p : ℚ) • (y : B))
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : ↥Λ → (V →ₗ[k] V))
    (hρadd : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    (hρ1 : ρ ⟨1, h1⟩ = LinearMap.id)
    (hρmul : ∀ x y : ↥Λ, ρ ⟨(x : B) * (y : B), hmulmem x y⟩ = (ρ y).comp (ρ x))
    (hV : Nontrivial V) :
    2 ≤ Module.finrank k V := by
  classical
  let ρ' : ↥Λ →+ (V →ₗ[k] V) := AddMonoidHom.mk' ρ hρadd
  have hρ' : ∀ x, ρ' x = ρ x := fun _ ↦ rfl

  have hker0 : ∀ x : ↥Λ, φ x = 0 → ρ x = 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := (hφker x).1 hx
    have hxy : x = (p : ℤ) • y := by
      apply Subtype.ext
      rw [Submodule.coe_smul, hy, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    rw [hxy, ← hρ', map_zsmul, hρ', ← Int.cast_smul_eq_zsmul k, Int.cast_natCast, CharP.cast_eq_zero,
      zero_smul]
  have hcongr : ∀ x y : ↥Λ, φ x = φ y → ρ x = ρ y := by
    intro x y h
    have h0 : ρ (x - y) = 0 := hker0 _ (by rw [map_sub, h, sub_self])
    rwa [← hρ', map_sub, sub_eq_zero, hρ', hρ'] at h0

  obtain ⟨e11, he11⟩ := hφsurj !![1, 0; 0, 0]
  obtain ⟨e22, he22⟩ := hφsurj !![0, 0; 0, 1]
  obtain ⟨e12, he12⟩ := hφsurj !![0, 1; 0, 0]
  obtain ⟨e21, he21⟩ := hφsurj !![0, 0; 1, 0]
  have hPQ : ρ e11 + ρ e22 = LinearMap.id := by
    rw [← hρ1, ← hρadd]
    apply hcongr
    rw [map_add, he11, he22, hφ1]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hTS : (ρ e21).comp (ρ e12) = ρ e11 := by
    rw [← hρmul]
    apply hcongr
    rw [hφmul, he12, he21, he11]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hST : (ρ e12).comp (ρ e21) = ρ e22 := by
    rw [← hρmul]
    apply hcongr
    rw [hφmul, he12, he21, he22]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hPQ0 : (ρ e11).comp (ρ e22) = 0 := by
    rw [← hρmul]
    apply hker0
    rw [hφmul, he11, he22]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

  haveI := hV
  have hid : (LinearMap.id : V →ₗ[k] V) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (by simpa using congrArg (fun f : V →ₗ[k] V ↦ f v) h)
  have hP : ρ e11 ≠ 0 := by
    intro hP0
    have hQ1 : ρ e22 = LinearMap.id := by rwa [hP0, zero_add] at hPQ
    have hT : ρ e21 = 0 := by
      calc ρ e21 = (ρ e21).comp ((ρ e12).comp (ρ e21)) := by rw [hST, hQ1, LinearMap.comp_id]
        _ = ((ρ e21).comp (ρ e12)).comp (ρ e21) := (LinearMap.comp_assoc _ _ _).symm
        _ = 0 := by rw [hTS, hP0, LinearMap.zero_comp]
    apply hid
    rw [← hQ1, ← hST, hT, LinearMap.comp_zero]
  have hQ : ρ e22 ≠ 0 := by
    intro hQ0
    have hP1 : ρ e11 = LinearMap.id := by rwa [hQ0, add_zero] at hPQ
    have hS : ρ e12 = 0 := by
      calc ρ e12 = (ρ e12).comp ((ρ e21).comp (ρ e12)) := by rw [hTS, hP1, LinearMap.comp_id]
        _ = ((ρ e12).comp (ρ e21)).comp (ρ e12) := (LinearMap.comp_assoc _ _ _).symm
        _ = 0 := by rw [hST, hQ0, LinearMap.zero_comp]
    apply hid
    rw [← hP1, ← hTS, hS, LinearMap.comp_zero]

  have hpos : ∀ f : V →ₗ[k] V, f ≠ 0 → 1 ≤ Module.finrank k (LinearMap.range f) := by
    intro f hf
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    exact hf
  have h1 : 1 ≤ Module.finrank k (LinearMap.range (ρ e11)) := hpos _ hP
  have h2 : 1 ≤ Module.finrank k (LinearMap.ker (ρ e11)) := by
    have hle : LinearMap.range (ρ e22) ≤ LinearMap.ker (ρ e11) := LinearMap.range_le_ker_iff.mpr hPQ0
    exact (hpos _ hQ).trans (Submodule.finrank_mono hle)
  have h3 := LinearMap.finrank_range_add_finrank_ker (ρ e11)
  omega

end MoritaAlg

namespace MoritaG

section Plumbing

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem eq_one_of_mul_self (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) (h : G.mul t x x = x) : x = G.one t := by
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t x) x := by rw [h]
    _ = G.one t := G.inv_mul_cancel t x

theorem one_comp_val (G : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) : ψ ≫ (G.one t).1 = (G.one (ψ ≫ t)).1 := by
  have := G.one_natural t (ψ ≫ t) ψ rfl
  exact (congrArg Subtype.val this)

end Plumbing

section FV

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type u} [Field k]
  {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] {E Eℓ : FakeEllipticCurve Λ N k}

noncomputable abbrev σ (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (frobenius k ℓ))

theorem pr_one (D : FrobeniusVerschiebungData ℓ E Eℓ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) :
    (Eℓ.L.one t').1 ≫ D.pr = (E.L.one (t' ≫ σ k ℓ)).1 := by
  let x : SchemeHomOver (t' ≫ σ k ℓ) E.f :=
    ⟨(Eℓ.L.one t').1 ≫ D.pr, by rw [Category.assoc, D.pr_isPullback.w, ← Category.assoc, (Eℓ.L.one t').2]⟩
  have hmul := D.pr_mul t' (Eℓ.L.one t') (Eℓ.L.one t')
  rw [Eℓ.L.one_mul] at hmul
  have hx : E.L.mul (t' ≫ σ k ℓ) x x = x := by
    apply Subtype.ext
    exact hmul.symm
  have := eq_one_of_mul_self E.L (t' ≫ σ k ℓ) x hx
  exact congrArg Subtype.val this

theorem F_one (D : FrobeniusVerschiebungData ℓ E Eℓ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    mapPt D.F D.F_over (E.L.one t) = Eℓ.L.one t := by
  have h := D.F_hom t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  exact eq_one_of_mul_self Eℓ.L t _ h.symm

theorem isIso_σ [IsAlgClosed k] : IsIso (σ k ℓ) := by
  haveI : PerfectRing k ℓ := PerfectRing.ofSurjective k ℓ fun x => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x (Fact.out : ℓ.Prime).pos
    exact ⟨z, by simpa [frobenius_def] using hz⟩
  have : CommRingCat.ofHom (frobenius k ℓ) = (frobeniusEquiv k ℓ).toCommRingCatIso.hom := rfl
  show IsIso (Spec.map (CommRingCat.ofHom (frobenius k ℓ)))
  rw [this]
  infer_instance

theorem σ_comp_eq_of_mapPt_F_eq_one (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
    (hQ : mapPt D.F D.F_over Q = Eℓ.L.one (𝟙 _)) :
    σ k ℓ ≫ Q.1 = (E.L.one (𝟙 (Spec (CommRingCat.of k)) ≫ σ k ℓ)).1 := by
  have hfrob := D.F_frobenius k Q.1
  have hQ1 : Q.1 ≫ D.F = (Eℓ.L.one (𝟙 _)).1 := congrArg Subtype.val hQ
  rw [← hfrob, ← Category.assoc, hQ1, pr_one D]

theorem forall_eq_one_of_isFrobeniusKernel [IsAlgClosed k]
    (D : FrobeniusVerschiebungData ℓ E Eℓ) (K : E.ExtraLevel ℓ)
    (hIFK : IsFrobeniusKernel (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) D) :
    ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
        FactorsThrough K.levK P → P = E.L.one (𝟙 (Spec (CommRingCat.of k))) := by
  intro P hP
  have h1 : mapPt D.F D.F_over P = Eℓ.L.one (𝟙 _) := (hIFK (𝟙 _) P).mp hP
  have hP' := σ_comp_eq_of_mapPt_F_eq_one D P h1
  have hone' := σ_comp_eq_of_mapPt_F_eq_one D (E.L.one (𝟙 _)) (F_one D (𝟙 _))
  haveI := isIso_σ (k := k) (ℓ := ℓ)
  apply Subtype.ext
  rw [← cancel_epi (σ k ℓ), hP', hone']

end FV

theorem degF_of_perfectField {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [PerfectField k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ) :
    IsFinite (pullback.fst D.F (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f) ∧
      LocallyOfFinitePresentation (pullback.fst D.F (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f) ∧
      ∀ s : ↥(Spec (CommRingCat.of k)), (pullback.fst D.F (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f).finrank s = ℓ ^ 2 := by
  haveI hsm : Smooth E.f := E.bundle.smooth
  haveI hsm2 : SmoothOfRelativeDimension 2 E.f :=
    CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two k E
  obtain ⟨hfin, hflat, hlofp, -⟩ :=
    AlgebraicGeometry.Smooth.isFinite_and_flat_and_surjective_of_isPullback_frobenius k ℓ E.f Eℓ.f D.pr
      D.pr_isPullback D.F D.F_over D.F_frobenius
  have hrank := AlgebraicGeometry.SmoothOfRelativeDimension.finrank_eq_pow_of_isPullback_frobenius k ℓ E.f Eℓ.f 2
    D.pr D.pr_isPullback D.F D.F_over D.F_frobenius

  have he : (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ Eℓ.f = 𝟙 _ :=
    (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).2
  have key : pullback.fst D.F (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f =
      pullback.snd D.F (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 := by
    calc pullback.fst D.F (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f
        = pullback.fst D.F (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ (D.F ≫ Eℓ.f) := by rw [D.F_over]
      _ = (pullback.snd D.F (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫
            (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1) ≫ Eℓ.f := by
          rw [← Category.assoc, pullback.condition]
      _ = pullback.snd D.F (Eℓ.L.one (𝟙 (Spec (CommRingCat.of k)))).1 := by
          rw [Category.assoc, he, Category.comp_id]
  rw [key]
  refine ⟨inferInstance, inferInstance, fun s ↦ ?_⟩
  rw [Scheme.Hom.finrank_pullback_snd]
  exact hrank _

section Forward

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (k : Type u) [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
  {E Eℓ : FakeEllipticCurve Λ N k} (D : FrobeniusVerschiebungData ℓ E Eℓ)
  (K : E.ExtraLevel ℓ)

theorem one_val_congr {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f)
    {T : Scheme.{u}} (s s' : T ⟶ Spec (CommRingCat.of k)) (h : s = s') : (G.one s).1 = (G.one s').1 := by
  subst h; rfl

theorem specMap_algebraMap_self : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [Algebra.algebraMap_self]
  change Spec.map (𝟙 (CommRingCat.of k)) = 𝟙 _
  exact Spec.map_id _

theorem mapPt_F_eq_one_of_factors
    {TH : Scheme.{u}} (tH : TH ⟶ Spec (CommRingCat.of k)) (Pu : SchemeHomOver tH E.f)
    (jK : TH ⟶ K.K) [IsIso jK] (hPu : Pu.1 = jK ≫ K.levK)
    (hkill : Pu.1 ≫ D.F = (Eℓ.L.one tH).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f)
    (hP : FactorsThrough K.levK P) : mapPt D.F D.F_over P = Eℓ.L.one t := by
  obtain ⟨P₀, hP₀⟩ := hP
  apply Subtype.ext
  simp only [mapPt_coe]
  have h1 : P.1 = (P₀ ≫ inv jK) ≫ Pu.1 := by
    rw [hPu, ← hP₀]; simp
  have h2 : (P₀ ≫ inv jK) ≫ tH = t := by
    have := Pu.2
    rw [hPu] at this
    rw [← P.2, ← hP₀]
    simp only [Category.assoc] at this ⊢
    rw [← this]; simp
  rw [h1, Category.assoc, hkill, one_comp_val, one_val_congr k Eℓ.L _ _ h2]

end Forward

section Forward2

theorem isFrobeniusKernel_of_forall_eq_one {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (K : E.ExtraLevel ℓ)
    (hK : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
        FactorsThrough K.levK P → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    IsFrobeniusKernel (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) D := by
  classical
  have hord := hΛ.isOrder

  have hK' : ∀ (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (ht : t = 𝟙 _) (P : SchemeHomOver t E.f),
      FactorsThrough K.levK P → P = E.L.one t := by
    rintro t rfl P; exact hK P
  have hK'' := hK' (Spec.map (CommRingCat.ofHom (algebraMap k k))) (specMap_algebraMap_self k)

  haveI : IsClosedImmersion K.levK := K.levK_closed
  haveI : IsFinite (K.levK ≫ E.f) := K.levK_finite
  obtain ⟨H, instCR, instHopf, hfin, hcoc, j, e, hjiso, hjf, hpts, hbij, hmulE, hnat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
      (k := k) E.L (fun t x y => E.comm t x y) K.levK
      (fun t => K.levK_one t) (fun t P Q hP hQ => K.levK_sub t P Q hP hQ)

  set tH : Spec (CommRingCat.of H) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k H)) with htH
  set tk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k)) with htk
  have htk1 : tk = 𝟙 _ := specMap_algebraMap_self k
  let u : WithConv (H →ₐ[k] H) := WithConv.toConv (AlgHom.id k H)
  let Pu : SchemeHomOver tH E.f := (e H u).val
  have hPu : Pu.1 = j ≫ K.levK := by
    show ((e H u).val).1 = _
    rw [hpts H u]
    simp [u]

  have hS : ∀ x y : {P : SchemeHomOver tk E.f // ∃ P₀ : _ ⟶ K.K, P₀ ≫ K.levK = P.1}, x = y := by
    intro x y
    apply Subtype.ext
    rw [hK'' x.val x.property, hK'' y.val y.property]
  have hconv_k : ∀ φ ψ : WithConv (H →ₐ[k] k), φ = ψ := fun φ ψ => (hbij k).1 (hS _ _)
  have halg_k : ∀ φ ψ : H →ₐ[k] k, φ = ψ := fun φ ψ => by
    have := hconv_k (WithConv.toConv φ) (WithConv.toConv ψ)
    simpa using this

  haveI : Nontrivial H := by
    by_contra htriv
    rw [not_nontrivial_iff_subsingleton] at htriv
    have h1 : (Bialgebra.counitAlgHom k H) 1 = 1 := map_one _
    have h0 : (Bialgebra.counitAlgHom k H) 1 = 0 := by
      rw [Subsingleton.elim (1 : H) 0, map_zero]
    exact one_ne_zero (h1 ▸ h0)
  haveI hlocal : IsLocalRing H := MoritaAlg.isLocalRing_of_subsingleton_algHom (k := k) ⟨halg_k⟩
  haveI : CharP H ℓ := charP_of_injective_algebraMap (algebraMap k H).injective ℓ
  have hrankH : Module.finrank k H = ℓ ^ 2 := by
    obtain ⟨s⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of k)))
    haveI : Flat (K.levK ≫ E.f) := K.levK_flat
    have h1 : (j ≫ K.levK ≫ E.f).finrank s = ℓ ^ 2 := by
      rw [Scheme.Hom.finrank_comp_left_of_isIso]; exact K.levK_rank s
    rw [hjf, Scheme.Hom.finrank_SpecMap_algebraMap] at h1
    haveI : Module.Free k H := Module.Free.of_divisionRing k H
    rwa [Module.rankAtStalk_eq_finrank_of_free] at h1

  have hact_mem : ∀ x : ↥Λ, ∃ P₀ : _ ⟶ K.K, P₀ ≫ K.levK = (pushPt (E.act x) (E.act_over x) Pu).1 :=
    fun x => K.levK_stable x tH Pu (e H u).property
  have hα : ∀ x : ↥Λ, ∃ αx : H →ₐ[k] H, (e H (WithConv.toConv αx)).val = pushPt (E.act x) (E.act_over x) Pu := by
    intro x
    obtain ⟨φ, hφ⟩ := (hbij H).2 ⟨pushPt (E.act x) (E.act_over x) Pu, hact_mem x⟩
    exact ⟨φ.ofConv, by simpa using congrArg Subtype.val hφ⟩
  choose α hαspec using hα

  have hnat_u : ∀ (g : H →ₐ[k] H), ((e H (WithConv.toConv g)).val).1 = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Pu.1 := by
    intro g
    have := hnat H H g u
    simpa [u] using this
  have hα1 : ∀ x : ↥Λ, Spec.map (CommRingCat.ofHom (α x).toRingHom) ≫ Pu.1 = Pu.1 ≫ E.act x := by
    intro x
    rw [← hnat_u (α x), hαspec x]
    rfl

  have hαε : ∀ (x : ↥Λ) (h : H), Coalgebra.counit (R := k) (α x h) = Coalgebra.counit h := by
    intro x h
    have := halg_k ((Bialgebra.counitAlgHom k H).comp (α x)) (Bialgebra.counitAlgHom k H)
    exact congrArg (fun (F : H →ₐ[k] k) => F h) this

  have hαadd : ∀ x y : ↥Λ, WithConv.toConv (α (x + y)) = WithConv.toConv (α x) * WithConv.toConv (α y) := by
    intro x y
    apply (hbij H).1
    apply Subtype.ext
    rw [hαspec, hmulE, hαspec, hαspec]
    exact E.act_add x y tH Pu

  have hαone : α ⟨1, hord.one_mem⟩ = AlgHom.id k H := by
    have h := hαspec ⟨1, hord.one_mem⟩
    have : pushPt (E.act ⟨1, hord.one_mem⟩) (E.act_over _) Pu = Pu := by
      apply Subtype.ext; simp [E.act_one hord.one_mem]
    rw [this] at h
    have : WithConv.toConv (α ⟨1, hord.one_mem⟩) = u := (hbij H).1 (Subtype.ext (by rw [h]))
    simpa [u] using this

  have hαmul : ∀ x y : ↥Λ, α ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hord.mul_mem x.2 y.2⟩ = (α y).comp (α x) := by
    intro x y
    have lhs := hαspec ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hord.mul_mem x.2 y.2⟩
    have rhs : ((e H (WithConv.toConv ((α y).comp (α x)))).val).1 =
        (pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hord.mul_mem x.2 y.2⟩) (E.act_over _) Pu).1 := by
      have := hnat H H (α y) (WithConv.toConv (α x))
      simp only [WithConv.ofConv_toConv] at this
      rw [this, hαspec x]
      simp only [mapPt_coe, pushPt, E.act_mul x y, ← Category.assoc, hα1 y]
    have : WithConv.toConv (α ⟨_, hord.mul_mem x.2 y.2⟩) = WithConv.toConv ((α y).comp (α x)) :=
      (hbij H).1 (Subtype.ext (Subtype.ext (by rw [lhs, rhs])))
    simpa using this

  set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom k H) with hI
  have hαI : ∀ x : ↥Λ, I ≤ I.comap (α x) := by
    intro x h hh
    simp only [hI, RingHom.mem_ker, Ideal.mem_comap] at hh ⊢
    change Coalgebra.counit (R := k) (α x h) = 0
    rw [hαε x h]; exact hh
  let ρ : ↥Λ → (I.Cotangent →ₗ[k] I.Cotangent) := fun x => Ideal.mapCotangent I I (α x) (hαI x)
  have hρtoC : ∀ (x : ↥Λ) (m : I), ρ x (I.toCotangent m) = I.toCotangent ⟨α x m, hαI x m.2⟩ :=
    fun x m => by simp [ρ, Ideal.mapCotangent_toCotangent]
  have hρadd : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y := by
    intro x y
    apply LinearMap.ext
    intro v
    obtain ⟨m, rfl⟩ := I.toCotangent_surjective v
    rw [LinearMap.add_apply, hρtoC, hρtoC, hρtoC, ← map_add, ← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero]
    have hconv := congrArg (fun (F : WithConv (H →ₐ[k] H)) => F.ofConv (m : H)) (hαadd x y)
    simp only [WithConv.ofConv_toConv] at hconv
    have := MoritaAlg.conv_sub_add_mem_sq (α x) (α y) (hαε x) (hαε y) m m.2
    rw [← hconv] at this
    simpa [sq] using this
  have hρone : ρ ⟨1, hord.one_mem⟩ = LinearMap.id := by
    apply LinearMap.ext; intro v
    obtain ⟨m, rfl⟩ := I.toCotangent_surjective v
    rw [hρtoC]; simp [hαone]
  have hρmul : ∀ x y : ↥Λ, ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hord.mul_mem x.2 y.2⟩ = (ρ y).comp (ρ x) := by
    intro x y
    apply LinearMap.ext; intro v
    obtain ⟨m, rfl⟩ := I.toCotangent_surjective v
    rw [LinearMap.comp_apply, hρtoC, hρtoC, hρtoC]
    congr 2
    simp [hαmul x y]

  haveI : IsNoetherianRing k := inferInstance
  haveI : Module.Finite k I := Module.Finite.of_injective ((Submodule.subtype I).restrictScalars k) Subtype.val_injective
  haveI : Module.Finite k I.Cotangent := Module.Finite.of_surjective ((I.toCotangent).restrictScalars k) I.toCotangent_surjective
  have hεsurj : Function.Surjective (Bialgebra.counitAlgHom k H) := fun r => ⟨algebraMap k H r, by simp⟩
  have hImax : I.IsMaximal := RingHom.ker_isMaximal_of_surjective (Bialgebra.counitAlgHom k H).toRingHom hεsurj
  have hIeq : I = IsLocalRing.maximalIdeal H := (IsLocalRing.eq_maximalIdeal hImax)
  haveI : Nontrivial I.Cotangent := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.cotangent_subsingleton_iff]
    intro hidem
    haveI : IsArtinianRing H := IsArtinianRing.of_finite k H
    haveI : IsNoetherianRing H := inferInstance
    rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing I).mp hidem with h0 | h1
    ·
      have hfield : Module.finrank k H = 1 := by
        have hbij : Function.Bijective (algebraMap k H) := by
          refine ⟨(algebraMap k H).injective, fun h => ⟨Coalgebra.counit (R := k) h, ?_⟩⟩
          have : h - algebraMap k H (Coalgebra.counit (R := k) h) ∈ I := by
            simp [hI, RingHom.mem_ker]
          rw [h0, Ideal.mem_bot, sub_eq_zero] at this
          exact this.symm
        have e := (AlgEquiv.ofBijective (Algebra.ofId k H) hbij).toLinearEquiv
        simpa using e.finrank_eq.symm
      rw [hfield] at hrankH
      have : 1 < ℓ ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : ℓ.Prime).one_lt
      omega
    · exact hImax.ne_top h1
  obtain ⟨φΛ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  have hdim : 2 ≤ Module.finrank k I.Cotangent :=
    MoritaAlg.two_le_finrank_of_antirep (k := k) ℓ Λ hord.one_mem (fun x y => hord.mul_mem x.2 y.2)
      φΛ (hφ1 hord.one_mem) (fun x y => hφmul x y _) hφsurj hφker I.Cotangent ρ hρadd hρone hρmul inferInstance

  have hpow : ∀ h ∈ I, h ^ ℓ = 0 := by
    set J : Ideal H := Ideal.span ((fun h : H => h ^ ℓ) '' (I : Set H)) with hJ
    have h905 := HopfAlgebra.finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent k ℓ H
    have hJbot : J = ⊥ := by
      have hq : Module.finrank k (H ⧸ J) + Module.finrank k (J.restrictScalars k) = Module.finrank k H := by
        rw [← (Submodule.Quotient.restrictScalarsEquiv k J).finrank_eq]
        exact Submodule.finrank_quotient_add_finrank _
      have h905' : Module.finrank k (H ⧸ J) = ℓ ^ Module.finrank k I.Cotangent := h905
      have hge : Module.finrank k H ≤ Module.finrank k (H ⧸ J) := by
        rw [hrankH, h905']
        exact Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos hdim
      have hJ0 : Module.finrank k (J.restrictScalars k) = 0 := by omega
      have hbot : J.restrictScalars k = ⊥ := Submodule.finrank_eq_zero.mp hJ0
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      have : x ∈ J.restrictScalars k := hx
      rw [hbot] at this
      simpa using this
    intro h hh
    have : h ^ ℓ ∈ J := Ideal.subset_span ⟨h, hh, rfl⟩
    rwa [hJbot, Ideal.mem_bot] at this

  have hfrobH : frobenius H ℓ = (algebraMap k H).comp ((frobenius k ℓ).comp (Bialgebra.counitAlgHom k H).toRingHom) := by
    apply RingHom.ext; intro h
    simp only [RingHom.coe_comp, Function.comp_apply, frobenius_def, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_pow]
    have hc : h - algebraMap k H (Bialgebra.counitAlgHom k H h) ∈ I := by simp [hI, RingHom.mem_ker]
    have := hpow _ hc
    have hsplit : h = algebraMap k H (Bialgebra.counitAlgHom k H h) + (h - algebraMap k H (Bialgebra.counitAlgHom k H h)) := by ring
    conv_lhs => rw [hsplit]
    rw [← frobenius_def, map_add, frobenius_def, frobenius_def, this, add_zero]

  have hkill : Pu.1 ≫ D.F = (Eℓ.L.one tH).1 := by
    apply D.pr_isPullback.hom_ext
    · rw [Category.assoc, D.F_frobenius H Pu.1, hfrobH]
      rw [pr_one D tH]
      simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      have hεu : Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom k H).toRingHom) ≫ Pu.1 = (E.L.one tk).1 := by
        have := hnat H k (Bialgebra.counitAlgHom k H) u
        simp only [u, WithConv.ofConv_toConv, AlgHom.comp_id] at this
        rw [← this]
        exact congrArg Subtype.val (hK'' _ (e k _).property)
      rw [hεu, one_comp_val, one_comp_val]
      apply one_val_congr
      rw [htk1]; simp [htH]
    · rw [Category.assoc, D.F_over, Pu.2, (Eℓ.L.one tH).2]

  have hfwd : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough K.levK P → mapPt D.F D.F_over P = Eℓ.L.one t :=
    fun t P hP => mapPt_F_eq_one_of_factors k D K tH Pu j hPu hkill t P hP

  obtain ⟨hdfin, hdlfp, hdrank⟩ :=
    degF_of_perfectField k ℓ E Eℓ D
  obtain ⟨K₀, hK₀, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq k ℓ hℓN hord E Eℓ
      D.F D.F_over D.V D.V_over D.F_hom D.V_hom D.F_act D.V_act D.V_F D.F_V D.F_lev hdfin hdlfp hdrank
      (by
        intro k' _ _ sk hℓ
        exfalso; apply hℓ
        rw [show (ℓ : k') = sk (ℓ : k) from (map_natCast sk ℓ).symm, CharP.cast_eq_zero k ℓ, map_zero])

  let Puniv : SchemeHomOver (K.levK ≫ E.f) E.f := ⟨K.levK, rfl⟩
  obtain ⟨i, hi⟩ := (hK₀ _ Puniv).mpr (hfwd _ Puniv ⟨𝟙 _, Category.id_comp _⟩)
  haveI : IsClosedImmersion K₀.levK := K₀.levK_closed
  haveI : IsClosedImmersion (i ≫ K₀.levK) := by rw [hi]; exact K.levK_closed
  haveI : IsClosedImmersion i := IsClosedImmersion.of_comp_isClosedImmersion i K₀.levK
  haveI : IsFinite (K₀.levK ≫ E.f) := K₀.levK_finite
  haveI : Flat (K₀.levK ≫ E.f) := K₀.levK_flat
  haveI : LocallyOfFinitePresentation (K₀.levK ≫ E.f) := K₀.levK_finitePresentation
  haveI : Flat (K.levK ≫ E.f) := K.levK_flat
  haveI : LocallyOfFinitePresentation (K.levK ≫ E.f) := K.levK_finitePresentation
  haveI : IsIso i :=
    AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq i (K₀.levK ≫ E.f) (K.levK ≫ E.f)
      (by rw [← Category.assoc, hi]) (fun s => by rw [K.levK_rank s, K₀.levK_rank s])

  intro T t P
  constructor
  · exact hfwd t P
  · intro hP
    obtain ⟨Q₀, hQ₀⟩ := (hK₀ t P).mpr hP
    have hlev : K.levK = i ≫ K₀.levK := hi.symm
    refine ⟨Q₀ ≫ inv i, ?_⟩
    show (Q₀ ≫ inv i) ≫ K.levK = P.1
    rw [hlev]; simp [hQ₀]

end Forward2

theorem main {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (K : E.ExtraLevel ℓ) :
    (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
        FactorsThrough K.levK P → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) ↔
      IsFrobeniusKernel (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) D :=
  ⟨isFrobeniusKernel_of_forall_eq_one k ℓ hℓN hΛ hB hℓq hℓq' E Eℓ D K,
   forall_eq_one_of_isFrobeniusKernel D K⟩

end MoritaG

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (K : E.ExtraLevel ℓ) :
    (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
        FactorsThrough K.levK P → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) ↔
      IsFrobeniusKernel (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) D :=
  MoritaG.main k ℓ hℓN hΛ hB hℓq hℓq' E Eℓ D K

end S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_eq_one_iff_isFrobeniusKernel
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_eq_one_iff_isFrobeniusKernel (solution)
