-- Prove2me | solution 1 for Deformation.DieudonneModule.natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/613e8dea-3b13-5fce-8123-19049c32ce81

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Theorems.Thm_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp
import Theorems.Thm_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
import Theorems.Thm_CartierDual_exists_equiv_algHom_monoidHom_units_of_isAlgClosed_of_charZero
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
import Theorems.Thm_CartierDual_isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

namespace HSDRParts

open Module

theorem pow_eq_pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {p : ℕ} {ζ : M} (hζ : ζ ^ p = 1) (m : ℕ) :
    ζ ^ m = ζ ^ (m % p) := by
  conv_lhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem pow_val_add {M : Type*} [CommMonoid M] {p : ℕ} [NeZero p] {ζ : M} (hζ : ζ ^ p = 1)
    (m n : ZMod p) : ζ ^ (m + n).val = ζ ^ m.val * ζ ^ n.val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod_of_pow_eq_one hζ]

theorem pow_val_natCast_mul {M : Type*} [CommMonoid M] {p : ℕ} [NeZero p] {ζ : M} (hζ : ζ ^ p = 1)
    (a : ℕ) (n : ZMod p) : ζ ^ ((a : ZMod p) * n).val = (ζ ^ n.val) ^ a := by
  rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, ← pow_eq_pow_mod_of_pow_eq_one hζ, pow_mul', ]

set_option maxHeartbeats 12800000 in

theorem S2_cycloDual (p : ℕ) [Fact p.Prime]
    {κ : Type} [Field κ] [Finite κ] [CharP κ p] [Algebra (ZMod p) κ]
    {N : Type} [AddCommGroup N] [Module κ N] [Module.Finite κ N]
    (L : Type) [Field L] (Γ : Type) [Group Γ] [MulSemiringAction Γ L]
    (ρ : Γ →* (N →ₗ[κ] N))
    (B : N →ₗ[κ] N →ₗ[κ] κ) (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBχ : ∀ (γ : Γ) (a : ℕ), (∀ μ : L, μ ^ p = 1 → γ • μ = μ ^ a) → ∀ x y, B (ρ γ x) (ρ γ y) = (a : κ) • B x y)
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ Φ : N ≃+ (N →+ Additive Lˣ),
      (∀ x y, ((Φ x y).toMul : L) = ζ ^ (Algebra.trace (ZMod p) κ (B x y)).val) ∧
      (∀ (γ : Γ) (x y : N), ((Φ (ρ γ x) (ρ γ y)).toMul : L) = γ • ((Φ x y).toMul : L)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  let ζu : Lˣ := Units.mk0 ζ hζ0
  have hζu : IsPrimitiveRoot ζu p := IsPrimitiveRoot.coe_units_iff.mp (by simpa [ζu] using hζ)
  have hζup : ζu ^ p = 1 := hζu.pow_eq_one
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one

  haveI : Module.Finite (ZMod p) κ := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (ZMod p) κ := inferInstance
  let T : κ →ₗ[ZMod p] ZMod p := Algebra.trace (ZMod p) κ
  have hTnd : ∀ b : κ, (∀ c : κ, T (c * b) = 0) → b = 0 := by
    intro b hb
    refine (traceForm_nondegenerate (ZMod p) κ).1 b fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm]; exact hb c

  let χ : N → N → Lˣ := fun x y => ζu ^ (T (B x y)).val
  have hχ : ∀ x y, ((χ x y : Lˣ) : L) = ζ ^ (T (B x y)).val := fun x y => by simp [χ, ζu]
  let Φ₁ : N →+ (N →+ Additive Lˣ) :=
    { toFun := fun x =>
        { toFun := fun y => Additive.ofMul (χ x y)
          map_zero' := by simp [χ]
          map_add' := fun y y' => by
            simp only [χ, map_add, ← ofMul_mul]; rw [pow_val_add hζup] }
      map_zero' := by ext y; simp [χ]
      map_add' := fun x x' => by
        ext y
        simp only [χ, map_add, LinearMap.add_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply,
          ← ofMul_mul]
        rw [pow_val_add hζup] }
  have hΦ₁ : ∀ x y, Φ₁ x y = Additive.ofMul (χ x y) := fun _ _ => rfl

  have hexp : ∀ n : ZMod p, ζu ^ n.val = 1 → n = 0 := by
    intro n hn
    have hdvd := (hζu.pow_eq_one_iff_dvd n.val).mp hn
    have hlt := ZMod.val_lt n
    have : n.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact (ZMod.val_eq_zero n).mp this

  have hinj : Function.Injective Φ₁ := by
    intro x x' hxx
    have h0 : Φ₁ (x - x') = 0 := by rw [map_sub, hxx, sub_self]
    have hz : x - x' = 0 := by
      apply hB
      intro y
      apply hTnd
      intro c
      have h1 : T (B (x - x') (c • y)) = 0 := by
        have := congrArg (fun f : N →+ Additive Lˣ => (f (c • y)).toMul) h0
        simp only [hΦ₁, toMul_ofMul, AddMonoidHom.zero_apply, toMul_zero] at this
        exact hexp _ this
      rwa [LinearMap.map_smul, smul_eq_mul] at h1
    exact sub_eq_zero.mp hz

  have hsurj : Function.Surjective Φ₁ := by
    intro χ'
    letI modN : Module (ZMod p) N := Module.compHom N (algebraMap (ZMod p) κ)
    haveI : IsScalarTower (ZMod p) κ N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : Module.Finite (ZMod p) N := Module.Finite.trans κ N

    have hval : ∀ y, (χ' y).toMul ∈ Subgroup.zpowers ζu := by
      intro y
      rw [hζu.zpowers_eq, mem_rootsOfUnity]
      have : χ' ((p : ℕ) • y) = (p : ℕ) • χ' y := map_nsmul χ' p y
      rw [← Nat.cast_smul_eq_nsmul κ, CharP.cast_eq_zero, zero_smul, map_zero] at this
      have h := congrArg Additive.toMul this
      rw [toMul_zero, toMul_nsmul] at h
      exact h.symm
    let lg : Additive ↥(Subgroup.zpowers ζu) ≃+ ZMod p := hζu.zmodEquivZPowers.symm
    let f : N →+ ZMod p :=
      { toFun := fun y => lg (Additive.ofMul ⟨(χ' y).toMul, hval y⟩)
        map_zero' := by
          have : (⟨(χ' 0).toMul, hval 0⟩ : ↥(Subgroup.zpowers ζu)) = 1 := Subtype.ext (by simp)
          rw [this, ofMul_one, map_zero]
        map_add' := fun y y' => by
          have : (⟨(χ' (y + y')).toMul, hval (y + y')⟩ : ↥(Subgroup.zpowers ζu)) =
              ⟨(χ' y).toMul, hval y⟩ * ⟨(χ' y').toMul, hval y'⟩ := Subtype.ext (by simp [toMul_add])
          rw [this, ofMul_mul, map_add] }
    have hf : ∀ y, ζu ^ (f y).val = (χ' y).toMul := by
      intro y
      have h1 : hζu.zmodEquivZPowers (f y) = Additive.ofMul ⟨(χ' y).toMul, hval y⟩ :=
        hζu.zmodEquivZPowers.apply_symm_apply _
      have h2 : hζu.zmodEquivZPowers (((f y).val : ℕ) : ZMod p) = Additive.ofMul ⟨ζu ^ (f y).val, _⟩ :=
        hζu.zmodEquivZPowers_apply_coe_nat (f y).val
      rw [ZMod.natCast_zmod_val] at h2
      have := h1.symm.trans h2
      exact (congrArg (fun z : Additive ↥(Subgroup.zpowers ζu) => ((Additive.toMul z : ↥(Subgroup.zpowers ζu)) : Lˣ)) this).symm
    let fₗ : N →ₗ[ZMod p] ZMod p := f.toZModLinearMap p
    have hfₗ : ∀ y, fₗ y = f y := fun _ => rfl

    haveI : Module.Finite (ZMod p) (N →ₗ[κ] κ) := Module.Finite.trans κ (N →ₗ[κ] κ)
    let Tstar : (N →ₗ[κ] κ) →ₗ[ZMod p] (N →ₗ[ZMod p] ZMod p) :=
      { toFun := fun g => T ∘ₗ (g.restrictScalars (ZMod p))
        map_add' := fun g g' => by ext y; simp
        map_smul' := fun c g => by
          ext y
          simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, LinearMap.smul_apply,
            RingHom.id_apply, map_smul] }
    have hTstar : ∀ g y, Tstar g y = T (g y) := fun _ _ => rfl
    have hTinj : Function.Injective Tstar := by
      intro g g' hgg
      have h0 : Tstar (g - g') = 0 := by rw [map_sub, hgg, sub_self]
      have : g - g' = 0 := by
        ext y
        apply hTnd
        intro c
        have := congrArg (fun h : N →ₗ[ZMod p] ZMod p => h (c • y)) h0
        simp only [hTstar, LinearMap.zero_apply, LinearMap.map_smul, smul_eq_mul] at this
        exact this
      exact sub_eq_zero.mp this
    have hdim : Module.finrank (ZMod p) (N →ₗ[κ] κ) = Module.finrank (ZMod p) (N →ₗ[ZMod p] ZMod p) := by
      rw [← Module.finrank_mul_finrank (ZMod p) κ (N →ₗ[κ] κ), Subspace.dual_finrank_eq, Subspace.dual_finrank_eq,
        Module.finrank_mul_finrank]
    obtain ⟨g, hg⟩ := (LinearMap.linearEquivOfInjective Tstar hTinj hdim).surjective fₗ
    have hg' : ∀ y, T (g y) = f y := fun y => by
      rw [← hTstar, ← hfₗ]; exact congrArg (fun h : N →ₗ[ZMod p] ZMod p => h y) hg

    have hBinj : Function.Injective (B : N →ₗ[κ] N →ₗ[κ] κ) := by
      intro x x' hxx
      have : x - x' = 0 := hB _ fun y => by rw [map_sub, hxx, sub_self, LinearMap.zero_apply]
      exact sub_eq_zero.mp this
    obtain ⟨x, hx⟩ := (LinearMap.linearEquivOfInjective B hBinj (Subspace.dual_finrank_eq).symm).surjective g
    refine ⟨x, ?_⟩
    ext y
    have hx' : B x = g := hx
    rw [hΦ₁, toMul_ofMul]
    show ((ζu ^ (T (B x y)).val : Lˣ) : L) = ((χ' y).toMul : L)
    rw [hx', hg', hf]

  let Φ : N ≃+ (N →+ Additive Lˣ) := AddEquiv.ofBijective Φ₁ ⟨hinj, hsurj⟩
  refine ⟨Φ, fun x y => by simpa [Φ, hΦ₁] using hχ x y, ?_⟩

  intro γ x y
  have hγζ : (γ • ζ) ^ p = 1 := by rw [← smul_pow', hζp, smul_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hγζ
  have hcyc : ∀ μ : L, μ ^ p = 1 → γ • μ = μ ^ a := by
    intro μ hμ
    obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
    rw [smul_pow', ← ha, ← pow_mul, ← pow_mul, mul_comm]
  have hB' := hBχ γ a hcyc x y
  have hT' : T (B (ρ γ x) (ρ γ y)) = (a : ZMod p) * T (B x y) := by
    rw [hB', smul_eq_mul, ← map_natCast (algebraMap (ZMod p) κ) a, ← Algebra.smul_def, map_smul, smul_eq_mul]
  show ((Φ₁ (ρ γ x) (ρ γ y)).toMul : L) = γ • ((Φ₁ x y).toMul : L)
  simp only [hΦ₁, toMul_ofMul, hχ]
  rw [hT', pow_val_natCast_mul hζp, smul_pow', ← ha, ← pow_mul, ← pow_mul, mul_comm]

end HSDRParts

open scoped TensorProduct

namespace HSDRGlue

section GaloisModule

variable {Γ : Type*} [Group Γ] {κ : Type*} [Field κ] {N : Type*} [AddCommGroup N] [Module κ N]

@[reducible] noncomputable def galoisModuleOfRep (ρ : Γ →* (N →ₗ[κ] N)) : DistribMulAction Γ N where
  smul σ x := ρ σ x
  one_smul x := by show ρ 1 x = x; rw [map_one]; rfl
  mul_smul σ τ x := by show ρ (σ * τ) x = ρ σ (ρ τ x); rw [map_mul]; rfl
  smul_zero σ := by show ρ σ 0 = 0; exact map_zero _
  smul_add σ x y := by show ρ σ (x + y) = ρ σ x + ρ σ y; exact map_add _ _ _

theorem galoisModuleOfRep_smul (ρ : Γ →* (N →ₗ[κ] N)) (σ : Γ) (x : N) :
    (letI := galoisModuleOfRep ρ; σ • x) = ρ σ x := rfl

end GaloisModule

section Rank

theorem exists_finrank_eq_prime_pow_of_equiv (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    {κ : Type} [Field κ] [Finite κ] [CharP κ p]
    {N : Type} [AddCommGroup N] [Module κ N] [Module.Finite κ N]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N) :
    ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) H = p ^ a := by
  classical
  have h1 := GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf p H
  rw [← h1, Nat.card_congr e]

  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  haveI : Fintype κ := Fintype.ofFinite κ
  haveI : Module.Finite (ZMod p) κ := Module.Finite.of_finite
  haveI : Finite N := Module.finite_of_finite κ
  haveI : Fintype N := Fintype.ofFinite N
  obtain ⟨n, hp, hn⟩ := FiniteField.card κ p
  refine ⟨(n : ℕ) * Module.finrank κ N, ?_⟩
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := κ) (V := N), hn, ← pow_mul]

end Rank

section BaseChange

variable {O : Type*} [CommRing O] (S : Type*) [CommRing S] [Algebra O S]
  {A B : Type*} [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

noncomputable def bialgEquivBaseChange (u : A ≃ₐc[O] B) : S ⊗[O] A ≃ₐc[S] S ⊗[O] B :=
  BialgEquiv.ofBialgHom
    (Bialgebra.TensorProduct.map (BialgHom.id S S) (u : A →ₐc[O] B))
    (Bialgebra.TensorProduct.map (BialgHom.id S S) (u.symm : B →ₐc[O] A))
    (by
      ext b
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul s x =>
        simp only [BialgHom.coe_comp, Function.comp_apply, BialgHom.coe_id, id_eq]
        erw [Bialgebra.TensorProduct.map_tmul]
        congr 1
        simp
      | add x y hx hy => simp only [map_add, hx, hy])
    (by
      ext a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul s x =>
        simp only [BialgHom.coe_comp, Function.comp_apply, BialgHom.coe_id, id_eq]
        erw [Bialgebra.TensorProduct.map_tmul]
        congr 1
        simp
      | add x y hx hy => simp only [map_add, hx, hy])

end BaseChange

end HSDRGlue

namespace HSDRGlue

section Points

open GaloisRep

variable (p : ℕ) [Fact p.Prime]

local notation "ℤp" => GaloisRep.ratLocalizedAt p
local notation "ℚbar" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

noncomputable def galTranslate {H : Type} [CommRing H] [Algebra ℤp H]
    (σ : Gal) (f : WithConv (H →ₐ[ℤp] ℚbar)) : WithConv (H →ₐ[ℤp] ℚbar) :=
  WithConv.toConv (((σ.restrictScalars ℤp : ℚbar ≃ₐ[ℤp] ℚbar) : ℚbar →ₐ[ℤp] ℚbar).comp (WithConv.ofConv f))

theorem galTranslate_apply {H : Type} [CommRing H] [Algebra ℤp H]
    (σ : Gal) (f : WithConv (H →ₐ[ℤp] ℚbar)) (h : H) :
    WithConv.ofConv (galTranslate p σ f) h = σ (WithConv.ofConv f h) := rfl

theorem galTranslate_mul {H : Type} [CommRing H] [Algebra ℤp H] (σ τ : Gal) (f : WithConv (H →ₐ[ℤp] ℚbar)) :
    galTranslate p (σ * τ) f = galTranslate p σ (galTranslate p τ f) := rfl

theorem galTranslate_one {H : Type} [CommRing H] [Algebra ℤp H] (f : WithConv (H →ₐ[ℤp] ℚbar)) :
    galTranslate p 1 f = f := rfl

theorem exists_equiv_points_cartierDual
    {H : Type} [CommRing H] [HopfAlgebra ℤp H] [Module.Finite ℤp H] [Module.Free ℤp H]
    [Coalgebra.IsCocomm ℤp H]
    {κ : Type} [Field κ] {N : Type} [AddCommGroup N] [Module κ N]
    (ρ : Gal →* (N →ₗ[κ] N))
    (e : WithConv (H →ₐ[ℤp] ℚbar) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_gal : ∀ (σ : Gal) (f g : WithConv (H →ₐ[ℤp] ℚbar)), (∀ h : H, g h = σ (f h)) → e g = ρ σ (e f))
    (d : WithConv (CartierDual ℤp H →ₐ[ℤp] ℚbar) ≃ (WithConv (H →ₐ[ℤp] ℚbar) →* (ℚbar)ˣ))
    (hd_mul : ∀ φ ψ, d (φ * ψ) = d φ * d ψ)
    (hd_gal : ∀ (σ : Gal) (φ φ' : WithConv (CartierDual ℤp H →ₐ[ℤp] ℚbar)), (∀ y, φ' y = σ (φ y)) →
      ∀ (f f' : WithConv (H →ₐ[ℤp] ℚbar)), (∀ x, f' x = σ (f x)) →
        ((d φ' f' : (ℚbar)ˣ) : ℚbar) = σ ((d φ f : (ℚbar)ˣ) : ℚbar))
    (Φ : N ≃+ (N →+ Additive (ℚbar)ˣ))
    (hΦ : ∀ (σ : Gal) (x y : N), ((Φ (ρ σ x) (ρ σ y)).toMul : ℚbar) = σ ((Φ x y).toMul : ℚbar)) :
    ∃ e₂ : WithConv (CartierDual ℤp H →ₐ[ℤp] ℚbar) ≃ N,
      (∀ φ ψ, e₂ (φ * ψ) = e₂ φ + e₂ ψ) ∧
      (∀ (σ : Gal) (φ φ' : WithConv (CartierDual ℤp H →ₐ[ℤp] ℚbar)), (∀ y, φ' y = σ (φ y)) →
        e₂ φ' = ρ σ (e₂ φ)) := by
  classical
  have he1 : e 1 = 0 := by
    have h := he_add 1 1
    rw [one_mul] at h
    have h2 : e 1 + e 1 = e 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hes0 : e.symm 0 = 1 := by apply e.injective; rw [Equiv.apply_symm_apply, he1]

  let T : (WithConv (H →ₐ[ℤp] ℚbar) →* (ℚbar)ˣ) ≃ (N →+ Additive (ℚbar)ˣ) :=
    { toFun := fun χ =>
        { toFun := fun y => Additive.ofMul (χ (e.symm y))
          map_zero' := by
            show Additive.ofMul (χ (e.symm 0)) = 0
            rw [hes0, map_one]; rfl
          map_add' := fun x y => by
            have : e.symm (x + y) = e.symm x * e.symm y := by
              apply e.injective; rw [Equiv.apply_symm_apply, he_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
            rw [this, map_mul]; rfl }
      invFun := fun χ =>
        { toFun := fun f => (χ (e f)).toMul
          map_one' := by
            show (χ (e 1)).toMul = 1
            rw [he1, map_zero]; rfl
          map_mul' := fun f g => by rw [he_add, map_add]; rfl }
      left_inv := fun χ => by ext f; simp
      right_inv := fun χ => by ext y; simp }
  have hT : ∀ χ y, ((T χ y).toMul : ℚbar) = ((χ (e.symm y) : (ℚbar)ˣ) : ℚbar) := fun χ y => rfl
  let e₂ : WithConv (CartierDual ℤp H →ₐ[ℤp] ℚbar) ≃ N := (d.trans T).trans Φ.symm.toEquiv
  have he₂ : ∀ φ, Φ (e₂ φ) = T (d φ) := fun φ => by
    show Φ (Φ.symm (T (d φ))) = T (d φ); exact Φ.apply_symm_apply _
  refine ⟨e₂, ?_, ?_⟩
  · intro φ ψ
    apply Φ.injective
    rw [map_add, he₂, he₂, he₂]
    erw [hd_mul]
    ext y
    rfl
  · intro σ φ φ' hφ'
    apply Φ.injective
    ext y

    have hy : ρ σ (ρ σ⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    have hpt : ∀ h : H, (e.symm y) h = σ ((galTranslate p σ⁻¹ (e.symm y)) h) := by
      intro h
      show (WithConv.ofConv (e.symm y)) h = σ (WithConv.ofConv (galTranslate p σ⁻¹ (e.symm y)) h)
      rw [galTranslate_apply]
      exact (σ.apply_symm_apply _).symm
    have hback : e.symm (ρ σ⁻¹ y) = galTranslate p σ⁻¹ (e.symm y) := by
      apply e.injective
      rw [Equiv.apply_symm_apply]
      refine (he_gal σ⁻¹ (e.symm y) _ (fun h => ?_)).trans (by rw [Equiv.apply_symm_apply])  |>.symm
      exact galTranslate_apply p σ⁻¹ (e.symm y) h

    have lhs : ((Φ (e₂ φ') y).toMul : ℚbar) = ((d φ' (e.symm y) : (ℚbar)ˣ) : ℚbar) := by rw [he₂]; exact hT _ _

    have rhs : ((Φ (ρ σ (e₂ φ)) y).toMul : ℚbar) = σ ((d φ (e.symm (ρ σ⁻¹ y)) : (ℚbar)ˣ) : ℚbar) := by
      conv_lhs => rw [← hy]
      rw [hΦ σ (e₂ φ) (ρ σ⁻¹ y), he₂]
      rfl
    have key : ((d φ' (e.symm y) : (ℚbar)ˣ) : ℚbar) = σ ((d φ (e.symm (ρ σ⁻¹ y)) : (ℚbar)ˣ) : ℚbar) := by
      rw [hback]
      exact hd_gal σ φ φ' hφ' (galTranslate p σ⁻¹ (e.symm y)) (e.symm y) hpt
    first
      | (rw [lhs, key, ← rhs])
      | exact Additive.toMul.injective (Units.ext (by rw [lhs, key, ← rhs]))

end Points

end HSDRGlue

open scoped TensorProduct in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hloc : IsLocalRing H) (hdual : IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H))
    {κ : Type} [Field κ] [Finite κ] [CharP κ p]
    {N : Type} [AddCommGroup N] [Module κ N] [Module.Finite κ N]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (N →ₗ[κ] N))
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = ρ σ (e f))
    (B : N →ₗ[κ] N →ₗ[κ] κ) (hB : ∀ x : N, (∀ y : N, B x y = 0) → x = 0)
    (hBχ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
        ∀ x y : N, B (ρ σ x) (ρ σ y) = (a : κ) • B x y) :
    Nat.card (Deformation.DieudonneModule.frobenius (ZMod p) p
        ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H)).ker =
      Nat.card (Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H) ⧸
        (Deformation.DieudonneModule.verschiebung (ZMod p) p
          ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H)).range) := by
  classical

  letI galN : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N := HSDRGlue.galoisModuleOfRep ρ

  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  obtain ⟨Φ, -, hΦ⟩ := HSDRParts.S2_cycloDual p (AlgebraicClosure ℚ) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    ρ B hB (fun σ a hσ x y => hBχ σ a hσ x y) ζ hζ

  obtain ⟨d, hd_mul, hgal⟩ := CartierDual.exists_equiv_algHom_monoidHom_units_of_isAlgClosed_of_charZero
    (GaloisRep.ratLocalizedAt p) H (AlgebraicClosure ℚ)
  have hd_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (φ φ' : WithConv (CartierDual (GaloisRep.ratLocalizedAt p) H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ y, φ' y = σ (φ y)) →
      ∀ (f f' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), (∀ x, f' x = σ (f x)) →
        ((d φ' f' : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = σ ((d φ f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) :=
    fun σ φ φ' hφ' f f' hf' => hgal (σ.restrictScalars (GaloisRep.ratLocalizedAt p)) φ φ' hφ' f f' hf'

  obtain ⟨e₂, he₂_add, he₂_act⟩ :=
    HSDRGlue.exists_equiv_points_cartierDual p ρ e he_add he_gal d hd_mul hd_gal Φ hΦ

  obtain hr₁ := HSDRGlue.exists_finrank_eq_prime_pow_of_equiv (κ := κ) p H e
  obtain hr₂ := HSDRGlue.exists_finrank_eq_prime_pow_of_equiv (κ := κ) p (CartierDual (GaloisRep.ratLocalizedAt p) H) e₂

  obtain ⟨⟨g, hg, -⟩, hbij⟩ :=
    HopfAlgebra.existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
      p hp2 H hr₁ e he_add (fun σ f g' h => he_gal σ f g' h)
      (CartierDual (GaloisRep.ratLocalizedAt p) H) hr₂ e₂ he₂_add (fun σ f g' h => he₂_act σ f g' h)
      (AddEquiv.refl N) (fun σ m => rfl)
  let u : CartierDual (GaloisRep.ratLocalizedAt p) H ≃ₐc[GaloisRep.ratLocalizedAt p] H :=
    BialgEquiv.ofBijective g (hbij g hg)

  obtain ⟨e₅, -⟩ := CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
    (GaloisRep.ratLocalizedAt p) (ZMod p) H
  have hself : Nonempty ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H ≃ₐc[ZMod p]
      CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H)) :=
    ⟨(HSDRGlue.bialgEquivBaseChange (ZMod p) u.symm).trans e₅.symm⟩

  obtain ⟨hl, hd⟩ := CartierDual.isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange p H (ZMod p)

  exact Deformation.DieudonneModule.natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp
    p _ (hl hloc) (hd hdual) hself

end S_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing
end P2MW
export P2MW.S_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing (solution)
