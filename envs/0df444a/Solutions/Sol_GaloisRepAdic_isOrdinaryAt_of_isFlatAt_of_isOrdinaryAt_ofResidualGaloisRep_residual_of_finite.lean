-- Prove2me | solution 1 for GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c5a39af4-c56b-5c6d-b863-5d85d86a96bb

import Definitions.Def_GaloisRep_Flat
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Projection
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Theorems.Thm_GaloisRepAdic_exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic
import Theorems.Thm_GaloisRepAdic_iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct

theorem eq_bot_of_finrank_zero {A : Type} [CommRing A] [Nontrivial A]
    {V : Type} [AddCommGroup V] [Module A V] (W : Submodule A V)
    [Module.Free A W] [Module.Finite A W] (h : Module.finrank A W = 0) : W = ⊥ := by
  have b := Module.Free.chooseBasis A W
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A W) = 0 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, h]
  haveI : IsEmpty (Module.Free.ChooseBasisIndex A W) := Fintype.card_eq_zero_iff.mp hcard
  haveI : Subsingleton W := b.repr.toEquiv.subsingleton
  exact (Submodule.eq_bot_iff _).mpr fun x hx => by
    have : (⟨x, hx⟩ : W) = 0 := Subsingleton.elim _ _
    simpa using congrArg Subtype.val this

theorem conj_mem_inertiaSubgroupIn_aux (P : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.decompositionSubgroup ℚ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    σ * τ * σ⁻¹ ∈ P.inertiaSubgroupIn ℚ := by
  have hNormal : (P.inertiaSubgroup ℚ).Normal := MonoidHom.normal_ker _
  obtain ⟨τ', hτ', rfl⟩ := Subgroup.mem_map.mp hτ
  have hmem : (⟨σ, hσ⟩ * τ' * ⟨σ, hσ⟩⁻¹ : P.decompositionSubgroup ℚ) ∈ P.inertiaSubgroup ℚ :=
    hNormal.conj_mem τ' hτ' ⟨σ, hσ⟩
  exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

theorem split_lemma {A : Type} [CommRing A] [IsLocalRing A] [Finite A]
    {V : Type} [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
    (hV : Module.finrank A V = 2) (J : Submodule A V) (φ : V →ₗ[A] V)
    (hφJ : ∀ v, φ v ∈ J) (hinj : ∀ x ∈ J, φ x = 0 → x = 0)
    (h1 : ¬ J ≤ maximalIdeal A • (⊤ : Submodule A V))
    (h2 : J ⊔ maximalIdeal A • (⊤ : Submodule A V) ≠ ⊤) :
    ∃ b : Module.Basis (Fin 2) A V, J = A ∙ b 0 := by
  classical
  haveI : Finite V := Module.finite_of_finite A

  let φJ : J →ₗ[A] J := φ.restrict (p := J) (q := J) (fun x _ => hφJ x)
  have hφJinj : Function.Injective φJ := by
    intro x y hxy
    have : φ (x - y : V) = 0 := by
      have := congrArg Subtype.val hxy
      simpa [φJ, map_sub, sub_eq_zero] using this
    exact Subtype.ext (sub_eq_zero.mp (hinj _ (J.sub_mem x.2 y.2) this))
  haveI : Finite J := Finite.of_injective _ Subtype.val_injective
  have hφJbij : Function.Bijective φJ := Finite.injective_iff_bijective.mp hφJinj
  let eJ : J ≃ₗ[A] J := LinearEquiv.ofBijective φJ hφJbij

  let π : V →ₗ[A] J := eJ.symm.toLinearMap ∘ₗ φ.codRestrict J hφJ
  have hπ : ∀ x : J, π x = x := by
    intro x
    apply eJ.injective
    simp only [π, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    ext; rfl
  have hcompl : IsCompl J (LinearMap.ker π) := LinearMap.isCompl_of_proj hπ

  set K := LinearMap.ker π
  haveI : Module.Finite A J := Module.Finite.of_injective J.subtype Subtype.val_injective
  haveI : Module.Finite A K := Module.Finite.of_injective K.subtype Subtype.val_injective
  let eVK : (J × K) ≃ₗ[A] V := Submodule.prodEquivOfIsCompl J K hcompl
  haveI : Module.Projective A (J × K) := Module.Projective.of_equiv eVK.symm
  haveI : Module.Projective A J := Module.Projective.of_split (LinearMap.inl A J K) (LinearMap.fst A J K) (by ext; simp)
  haveI : Module.Projective A K := Module.Projective.of_split (LinearMap.inr A J K) (LinearMap.snd A J K) (by ext; simp)
  haveI : Module.Free A J := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free A K := Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank A J + Module.finrank A K = 2 := by
    rw [← Module.finrank_prod, eVK.finrank_eq, hV]
  have hJ0 : Module.finrank A J ≠ 0 := by
    intro h0
    have := eq_bot_of_finrank_zero J h0
    exact h1 (this ▸ bot_le)
  have hK0 : Module.finrank A K ≠ 0 := by
    intro h0
    have hK := eq_bot_of_finrank_zero K h0
    have : J = ⊤ := by simpa [hK] using hcompl.sup_eq_top
    exact h2 (by simp [this])
  have hJ1 : Module.finrank A J = 1 := by omega
  have hK1 : Module.finrank A K = 1 := by omega

  let bJ : Module.Basis (Fin 1) A J := (Module.Free.chooseBasis A J).reindex
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_chooseBasisIndex, hJ1]))
  let bK : Module.Basis (Fin 1) A K := (Module.Free.chooseBasis A K).reindex
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_chooseBasisIndex, hK1]))
  let b : Module.Basis (Fin 2) A V := ((bJ.prod bK).map eVK).reindex finSumFinEquiv
  refine ⟨b, ?_⟩
  have hb0 : b 0 = (bJ 0 : V) := by
    have : ((finSumFinEquiv (m := 1) (n := 1)).symm (0 : Fin 2)) = Sum.inl (0 : Fin 1) := by decide
    simp [b, Module.Basis.reindex_apply, this, Module.Basis.prod_apply, eVK,
      Submodule.coe_prodEquivOfIsCompl']
  rw [hb0]
  apply le_antisymm
  · intro x hx
    have hrepr := bJ.mem_span (⟨x, hx⟩ : J)
    have : (⟨x, hx⟩ : J) ∈ A ∙ bJ 0 := by
      have hr : Set.range bJ = {bJ 0} := by
        ext y; simp [Fin.exists_fin_one, eq_comm]
      simpa [hr] using bJ.mem_span ⟨x, hx⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
    exact Submodule.mem_span_singleton.mpr ⟨a, by simpa using congrArg Subtype.val ha⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact (bJ 0).2

theorem residual_facts {A : Type} [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (ρ : GaloisRepAdic A) (hdet : ρ.DetIsCyclotomic p)
    (hres : (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V,
        ρ.ρ σ₀ (ρ.ρ σ v - v) - (2 : A) • (ρ.ρ σ v - v) ∈
          maximalIdeal A • (⊤ : Submodule A ρ.V)) ∧
      ¬ (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ σ - LinearMap.id)) ≤
          maximalIdeal A • (⊤ : Submodule A ρ.V) ∧
      (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ σ - LinearMap.id)) ⊔
          maximalIdeal A • (⊤ : Submodule A ρ.V) ≠ ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  let ρb := GaloisRepAdic.ofResidualGaloisRep ρ.residual
  have hdetb : ρb.DetIsCyclotomic p :=
    GaloisRepAdic.detIsCyclotomic_baseChangeAlong (IsLocalRing.residue A) inferInstance ρ hdet
  obtain ⟨bb, hJb, hωb⟩ :=
    GaloisRepAdic.exists_basis_iSup_range_sub_one_eq_span_of_isOrdinaryAt_of_detIsCyclotomic
      p hp2 ρb hdetb hres P hP

  have h2p : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hcop : Nat.Coprime 2 (p ^ 1) := by
    rw [pow_one]; exact (Nat.coprime_primes Nat.prime_two hp).mpr (ne_of_lt h2p)
  obtain ⟨σ₀, hσ₀, hσ₀μ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one P hp hP 1
      (ZMod.unitOfCoprime 2 hcop)
  have hval : ((ZMod.unitOfCoprime 2 hcop : (ZMod (p ^ 1))ˣ) : ZMod (p ^ 1)).val = 2 := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, pow_one]; exact Nat.mod_eq_of_lt h2p
  have hσ₀b : ρb.ρ σ₀ (bb 0) = (2 : ResidueField A) • bb 0 := by
    have h3 := hωb σ₀ hσ₀ 2 (fun μ hμ => by
      have h4 := hσ₀μ μ (by simpa using hμ); rwa [hval] at h4)
    simpa using h3

  let π : ρ.V →+ ρb.V :=
    { toFun := fun v => ((1 : ResidueField A) ⊗ₜ[A] v : ResidueField A ⊗[A] ρ.V)
      map_zero' := TensorProduct.tmul_zero _ _
      map_add' := fun v w => TensorProduct.tmul_add _ _ _ }
  have hπ : ∀ v, π v = ((1 : ResidueField A) ⊗ₜ[A] v : ResidueField A ⊗[A] ρ.V) := fun _ => rfl
  have hπsmul : ∀ (a : A) (v : ρ.V), π (a • v) = (IsLocalRing.residue A a) • π v := by
    intro a v
    show ((1 : ResidueField A) ⊗ₜ[A] (a • v) : ResidueField A ⊗[A] ρ.V) =
      (IsLocalRing.residue A a) • ((1 : ResidueField A) ⊗ₜ[A] v)
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    congr 1
  have hπρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V),
      π (ρ.ρ σ v) = ρb.ρ σ (π v) := fun σ v => by
    show ((1 : ResidueField A) ⊗ₜ[A] (ρ.ρ σ v) : ResidueField A ⊗[A] ρ.V) =
      (ρ.ρ σ).baseChange (ResidueField A) ((1 : ResidueField A) ⊗ₜ[A] v)
    rw [LinearMap.baseChange_tmul]
  have hEπ : ∀ v, (TensorProduct.quotTensorEquivQuotSMul ρ.V (maximalIdeal A)) (π v) =
      Submodule.Quotient.mk v := by
    intro v
    show (TensorProduct.quotTensorEquivQuotSMul ρ.V (maximalIdeal A))
      ((Ideal.Quotient.mk (maximalIdeal A) 1) ⊗ₜ v) = _
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have hker : ∀ v, π v = 0 ↔ v ∈ maximalIdeal A • (⊤ : Submodule A ρ.V) := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← hEπ, LinearEquiv.map_eq_zero_iff]; exact Iff.rfl
  have hπsurj : Function.Surjective π := by
    intro w
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _
      ((TensorProduct.quotTensorEquivQuotSMul ρ.V (maximalIdeal A)) w)
    exact ⟨v, (TensorProduct.quotTensorEquivQuotSMul ρ.V (maximalIdeal A)).injective
      (by rw [hEπ, hv])⟩

  have hdisp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V,
      π (ρ.ρ σ v - v) ∈ (ResidueField A) ∙ bb 0 := by
    intro σ hσ v
    rw [← hJb]
    refine Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ ⟨π v, ?_⟩)
    rw [map_sub, hπρ]; rfl
  refine ⟨σ₀, hσ₀, ?_, ?_, ?_⟩
  ·
    intro σ hσ v
    rw [← hker, map_sub, hπρ, hπsmul, map_ofNat]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hdisp σ hσ v)
    rw [← hc, map_smul, hσ₀b, smul_comm c (2 : ResidueField A), sub_self]
  ·
    intro hle
    have htriv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : ρb.V, ρb.ρ σ w - w = 0 := by
      intro σ hσ w
      obtain ⟨v, rfl⟩ := hπsurj w
      have hvJ : ρ.ρ σ v - v ∈
          (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ σ - LinearMap.id)) :=
        Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ ⟨v, rfl⟩)
      have h0 := (hker _).mpr (hle hvJ)
      rw [map_sub, hπρ] at h0
      exact h0
    have hbot : (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρb.ρ σ - LinearMap.id)) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
      refine Submodule.iSup_induction _ (motive := fun w => w = 0) hw ?_ rfl
        (fun x y hx hy => by rw [hx, hy, add_zero])
      intro σ w hw
      refine Submodule.iSup_induction _ (motive := fun w => w = 0) hw ?_ rfl
        (fun x y hx hy => by rw [hx, hy, add_zero])
      intro hσ w hw
      obtain ⟨u, rfl⟩ := hw
      simpa using htriv σ hσ u
    rw [hJb] at hbot
    have : bb 0 = 0 := by
      have hm : bb 0 ∈ (ResidueField A) ∙ bb 0 := Submodule.mem_span_singleton_self _
      rw [hbot] at hm; exact (Submodule.mem_bot _).mp hm
    exact bb.ne_zero 0 this
  ·
    intro htop
    have hall : ∀ w : ρb.V, w ∈ (ResidueField A) ∙ bb 0 := by
      intro w
      obtain ⟨v, rfl⟩ := hπsurj w
      have hv : v ∈ (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ σ - LinearMap.id)) ⊔
          maximalIdeal A • (⊤ : Submodule A ρ.V) := by rw [htop]; exact Submodule.mem_top
      obtain ⟨j, hj, m, hm, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, (hker m).mpr hm, add_zero]
      refine Submodule.iSup_induction _ (motive := fun j => π j ∈ (ResidueField A) ∙ bb 0) hj
        ?_ (by show π 0 ∈ _; rw [π.map_zero]; exact Submodule.zero_mem _)
        (fun x y hx hy => by show π (x + y) ∈ _; rw [π.map_add]; exact Submodule.add_mem _ hx hy)
      intro σ j hj
      refine Submodule.iSup_induction _ (motive := fun j => π j ∈ (ResidueField A) ∙ bb 0) hj
        ?_ (by show π 0 ∈ _; rw [π.map_zero]; exact Submodule.zero_mem _)
        (fun x y hx hy => by show π (x + y) ∈ _; rw [π.map_add]; exact Submodule.add_mem _ hx hy)
      intro hσ j hj
      obtain ⟨u, rfl⟩ := hj
      exact hdisp σ hσ u
    have h1mem := hall (bb 1)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1mem
    have := congrArg (fun w => bb.repr w 1) hc
    simp [Module.Basis.repr_self] at this

theorem kf_step {A : Type} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (ρ : GaloisRepAdic A) (hpA : (p : A) ∈ maximalIdeal A) (hflat : ρ.IsFlatAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ₀ : σ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hkill : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V,
        ρ.ρ σ₀ (ρ.ρ σ v - v) - (2 : A) • (ρ.ρ σ v - v) ∈
          maximalIdeal A • (⊤ : Submodule A ρ.V))
    (j : ℕ) (x : ρ.V)
    (hxJ : x ∈ ⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ σ - LinearMap.id))
    (hxj : x ∈ maximalIdeal A ^ j • (⊤ : Submodule A ρ.V)) :
    ρ.ρ σ₀ x - (2 : A) • x ∈ maximalIdeal A ^ (j + 1) • (⊤ : Submodule A ρ.V) := by
  classical
  set I : Ideal A := maximalIdeal A ^ (j + 1) with hI
  haveI : Finite (A ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective

  let Q := ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))
  let mk : ρ.V →ₗ[A] Q := (I • (⊤ : Submodule A ρ.V)).mkQ
  let L : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → (Q →ₗ[A] Q) := fun σ => ρ.levelAction I σ
  have hLmk : ∀ σ v, L σ (mk v) = mk (ρ.ρ σ v) := fun σ v => rfl
  let D : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → (Q →ₗ[A] Q) :=
    fun σ => ρ.levelAction I σ - LinearMap.id

  let N : Submodule A Q := maximalIdeal A ^ j • (⊤ : Submodule A Q)
  have hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, N.map (ρ.levelAction I σ) ≤ N := by
    intro σ
    show (maximalIdeal A ^ j • (⊤ : Submodule A Q)).map (L σ) ≤ _
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top

  have hFF := GaloisRepAdic.iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level ρ p hp2 hpA I
    (hflat.2 I inferInstance) P hP N hN

  have hmkJ : mk x ∈ ⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.levelAction I σ - LinearMap.id) := by
    refine Submodule.iSup_induction _
      (motive := fun y => mk y ∈ ⨆ σ ∈ P.inertiaSubgroupIn ℚ,
        LinearMap.range (ρ.levelAction I σ - LinearMap.id)) hxJ ?_
      (by show mk 0 ∈ _; rw [map_zero]; exact Submodule.zero_mem _)
      (fun y z hy hz => by show mk (y + z) ∈ _; rw [map_add]; exact Submodule.add_mem _ hy hz)
    intro σ y hy
    refine Submodule.iSup_induction _
      (motive := fun y => mk y ∈ ⨆ σ ∈ P.inertiaSubgroupIn ℚ,
        LinearMap.range (ρ.levelAction I σ - LinearMap.id)) hy ?_
      (by show mk 0 ∈ _; rw [map_zero]; exact Submodule.zero_mem _)
      (fun y z hy hz => by show mk (y + z) ∈ _; rw [map_add]; exact Submodule.add_mem _ hy hz)
    intro hσ y hy
    obtain ⟨u, rfl⟩ := hy
    refine Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ ⟨mk u, ?_⟩)
    show L σ (mk u) - mk u = mk (ρ.ρ σ u - u)
    rw [hLmk, map_sub]
  have hmkN : mk x ∈ N := by
    have : (maximalIdeal A ^ j • (⊤ : Submodule A ρ.V)).map mk ≤ N := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact this ⟨x, hxj, rfl⟩
  have hmk : mk x ∈ ⨆ σ ∈ P.inertiaSubgroupIn ℚ, N.map (ρ.levelAction I σ - LinearMap.id) := by
    rw [← hFF]; exact ⟨hmkJ, hmkN⟩

  let T : Q →ₗ[A] Q := L σ₀ - (2 : A) • (LinearMap.id : Q →ₗ[A] Q)
  have hTmk : ∀ w, T (mk w) = mk (ρ.ρ σ₀ w - (2 : A) • w) := by
    intro w
    show L σ₀ (mk w) - (2 : A) • mk w = mk (ρ.ρ σ₀ w - (2 : A) • w)
    rw [hLmk, map_sub, map_smul]
  have hItop : I • (⊤ : Submodule A Q) = ⊥ := by
    have h := Submodule.map_smul'' I (⊤ : Submodule A ρ.V) mk
    rw [Submodule.map_top, Submodule.range_mkQ] at h
    rw [← h]
    exact Submodule.mkQ_map_self _
  have hkillQ : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ q : Q,
      T (D σ q) ∈ maximalIdeal A • (⊤ : Submodule A Q) := by
    intro σ hσ q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have e1 : D σ (mk v) = mk (ρ.ρ σ v - v) := by
      show L σ (mk v) - mk v = mk (ρ.ρ σ v - v); rw [hLmk, map_sub]
    show T (D σ (mk v)) ∈ _
    rw [e1, hTmk]
    have : (maximalIdeal A • (⊤ : Submodule A ρ.V)).map mk ≤ maximalIdeal A • (⊤ : Submodule A Q) := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact this ⟨_, hkill σ hσ v, rfl⟩
  have hTle : (⨆ σ ∈ P.inertiaSubgroupIn ℚ, N.map (ρ.levelAction I σ - LinearMap.id)) ≤
      LinearMap.ker T := by
    refine iSup₂_le fun σ hσ => ?_
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.smul_le.mpr fun a ha q _ => ?_
    show T (D σ (a • q)) = 0
    rw [map_smul, map_smul]
    have hmem : a • T (D σ q) ∈ (maximalIdeal A ^ j * maximalIdeal A) • (⊤ : Submodule A Q) := by
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul ha (hkillQ σ hσ q)
    have hIeq : maximalIdeal A ^ j * maximalIdeal A = I := (pow_succ _ _).symm
    rw [hIeq, hItop] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have hT0 : T (mk x) = 0 := hTle hmk
  rw [hTmk] at hT0
  have : ρ.ρ σ₀ x - (2 : A) • x ∈ LinearMap.ker mk := hT0
  rwa [Submodule.ker_mkQ] at this

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic A) (hdet : ρ.DetIsCyclotomic p) (hflat : ρ.IsFlatAt p)
    (hres : (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsOrdinaryAt p) :
    ρ.IsOrdinaryAt p := by
  classical
  have hp : p.Prime := Fact.out
  intro P hP
  let J : Submodule A ρ.V := ⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ σ - LinearMap.id)
  have hJmem : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ J := fun σ hσ v =>
    Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ ⟨v, rfl⟩)
  have hconj : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      σ * τ * σ⁻¹ ∈ P.inertiaSubgroupIn ℚ := fun σ hσ τ hτ => conj_mem_inertiaSubgroupIn_aux P σ hσ τ hτ
  have hJD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ J, ρ.ρ σ v ∈ J := by
    intro σ hσ v hv
    suffices h : J.map (ρ.ρ σ) ≤ J from h ⟨v, hv, rfl⟩
    simp only [J, Submodule.map_iSup]
    refine iSup₂_le fun τ hτ => ?_
    have hστ := hconj σ hσ τ hτ
    have hmul : ρ.ρ (σ * τ * σ⁻¹) * ρ.ρ σ = ρ.ρ σ * ρ.ρ τ := by
      rw [← map_mul, ← map_mul, inv_mul_cancel_right]
    have heq : (ρ.ρ σ).comp (ρ.ρ τ - LinearMap.id) =
        (ρ.ρ (σ * τ * σ⁻¹) - LinearMap.id).comp (ρ.ρ σ) := by
      ext w
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
      rw [← Module.End.mul_apply, ← hmul, Module.End.mul_apply]
    rw [← LinearMap.range_comp, heq]
    exact (LinearMap.range_comp_le_range _ _).trans
      (le_iSup₂_of_le (σ * τ * σ⁻¹) hστ le_rfl)
  have hbasis : ∃ b : Module.Basis (Fin 2) A ρ.V, J = A ∙ b 0 := by
    have hpA : (p : A) ∈ maximalIdeal A := hdet.1
    obtain ⟨σ₀, hσ₀, hkill, h1, h2⟩ := residual_facts p hp2 ρ hdet hres P hP
    let φ : ρ.V →ₗ[A] ρ.V := ρ.ρ σ₀ - LinearMap.id
    have hφJ : ∀ v, φ v ∈ J := fun v => hJmem σ₀ hσ₀ v

    obtain ⟨r, hr⟩ : ∃ r : ℕ, maximalIdeal A ^ r = ⊥ := by
      obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
      refine ⟨r, ?_⟩
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hr
    have hinj : ∀ x ∈ J, φ x = 0 → x = 0 := by
      intro x hxJ hφx
      have hfix : ρ.ρ σ₀ x = x := sub_eq_zero.mp hφx
      have hall : ∀ j : ℕ, x ∈ maximalIdeal A ^ j • (⊤ : Submodule A ρ.V) := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          have h := kf_step p hp2 ρ hpA hflat P hP σ₀ hσ₀ hkill j x hxJ ih
          rw [hfix, two_smul] at h
          have e : x - (x + x) = -x := by abel
          rw [e] at h
          exact (Submodule.neg_mem_iff _).mp h
      have hx := hall r
      rw [hr, Submodule.bot_smul] at hx
      exact (Submodule.mem_bot _).mp hx
    exact split_lemma ρ.finrank_eq J φ hφJ hinj h1 h2
  obtain ⟨b, hb⟩ := hbasis
  exact ⟨J, ⟨b, hb⟩, hJD, fun σ hσ v => hJmem σ hσ v⟩

end S_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite
end P2MW
export P2MW.S_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite (solution)
