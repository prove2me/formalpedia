-- Prove2me | solution 1 for GaloisRep.exists_finiteFlat_of_subalgebra_pi_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/040fc595-ed67-5339-b370-d1cef88b9421

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace P2mHopfOrder

abbrev Γℚ : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

abbrev Qb : Type := AlgebraicClosure ℚ

abbrev Rp (p : ℕ) : Type := GaloisRep.ratLocalizedAt p

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

scoped instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

theorem injective_of_linearIndependent_basis {R V W ι : Type} [CommRing R] [AddCommGroup V]
    [Module R V] [AddCommGroup W] [Module R W] (b : Module.Basis ι R V) (f : V →ₗ[R] W)
    (h : LinearIndependent R (fun i => f (b i))) : Function.Injective f := by
  intro v w hvw
  have key : ∀ u, f u = Finsupp.linearCombination R (fun i => f (b i)) (b.repr u) := fun u => by
    conv_lhs => rw [← b.linearCombination_repr u]
    rw [Finsupp.apply_linearCombination]
    rfl
  rw [key v, key w] at hvw
  exact b.repr.injective (h hvw)

theorem linearIndependent_mul {L X Y ι κ : Type} [Field L] [Fintype ι] [Fintype κ]
    (v : ι → X → L) (w : κ → Y → L) (hv : LinearIndependent L v) (hw : LinearIndependent L w) :
    LinearIndependent L (fun ij : ι × κ => fun xy : X × Y => v ij.1 xy.1 * w ij.2 xy.2) := by
  rw [Fintype.linearIndependent_iff] at hv hw ⊢
  intro g hg
  have h1 : ∀ (i : ι) (y : Y), ∑ j, g (i, j) * w j y = 0 := by
    intro i y
    have h2 : ∑ i, (∑ j, g (i, j) * w j y) • v i = 0 := by
      funext x
      have h3 := congrFun hg (x, y)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h3 ⊢
      rw [← h3, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    exact hv _ h2 i
  rintro ⟨i, j⟩
  have h4 : ∑ j, g (i, j) • w j = 0 := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact h1 i y
  exact hw _ h4 j

section setting

variable {p : ℕ} (hp : p.Prime) {X : Type} [AddCommGroup X]
  [DistribMulAction Γℚ X] (B : Subalgebra (Rp p) (X → Qb))

theorem subring_smul_eq (r : Rp p) (v : Qb) : r • v = algebraMap (Rp p) Qb r * v :=
  Algebra.smul_def r v

theorem algebraMap_injective : Function.Injective (algebraMap (Rp p) Qb) := by
  rw [IsScalarTower.algebraMap_eq (Rp p) ℚ Qb]
  exact (algebraMap ℚ Qb).injective.comp Subtype.val_injective

scoped instance isTorsionFree_pi : Module.IsTorsionFree (Rp p) (X → Qb) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r F hrF => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  · refine Or.inr (funext fun x => ?_)
    have h1 := congrFun hrF x
    rw [Pi.smul_apply, Algebra.smul_def, Pi.zero_apply, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd (algebraMap_injective (by rw [h1, map_zero])) hr
    · exact h1

scoped instance isTorsionFree_B : Module.IsTorsionFree (Rp p) B :=
  Function.Injective.moduleIsTorsionFree (fun F : B => (F : X → Qb)) Subtype.val_injective
    fun _ _ => rfl

def precomp {Y Z : Type} (π : Z → Y) : (Y → Qb) →ₐ[Rp p] (Z → Qb) where
  toFun F := fun z => F (π z)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[scoped simp] theorem precomp_apply {Y Z : Type} (π : Z → Y) (F : Y → Qb) (z : Z) :
    precomp (p := p) π F z = F (π z) := rfl

def incl {Y : Type} (π : Y → X) : B →ₐ[Rp p] (Y → Qb) := (precomp π).comp B.val

@[scoped simp] theorem incl_apply {Y : Type} (π : Y → X) (F : B) (y : Y) : incl B π F y = (F : X → Qb) (π y) :=
  rfl

def θ₂ : B ⊗[Rp p] B →ₐ[Rp p] (X × X → Qb) :=
  Algebra.TensorProduct.productMap (incl B Prod.fst) (incl B Prod.snd)

theorem θ₂_tmul (F F' : B) (xy : X × X) :
    θ₂ B (F ⊗ₜ F') xy = (F : X → Qb) xy.1 * (F' : X → Qb) xy.2 := rfl

def θ₃ : B ⊗[Rp p] (B ⊗[Rp p] B) →ₐ[Rp p] (X × (X × X) → Qb) :=
  Algebra.TensorProduct.productMap (incl B Prod.fst)
    ((precomp (fun t : X × (X × X) => t.2)).comp (θ₂ B))

theorem θ₃_tmul (F : B) (T : B ⊗[Rp p] B) (t : X × (X × X)) :
    θ₃ B (F ⊗ₜ T) t = (F : X → Qb) t.1 * θ₂ B T t.2 := rfl

structure IsHopfOrder : Prop where
  fg : (Subalgebra.toSubmodule B).FG
  equiv : ∀ F ∈ B, ∀ (σ : Γℚ) (x : X), F (σ • x) = σ (F x)
  comul : ∀ F ∈ B, ∃ (n : ℕ) (F₁ F₂ : Fin n → X → Qb),
    (∀ i, F₁ i ∈ B) ∧ (∀ i, F₂ i ∈ B) ∧ ∀ x y : X, F (x + y) = ∑ i, F₁ i x * F₂ i y
  neg : ∀ F ∈ B, (fun x => F (-x)) ∈ B
  sep : ∀ x y : X, (∀ F ∈ B, F x = F y) → x = y

variable {B} [Finite X] (H : IsHopfOrder B)

include hp H

theorem moduleFinite : Module.Finite (Rp p) B := Module.Finite.iff_fg.mpr H.fg

theorem moduleFree : Module.Free (Rp p) B := by
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp
  haveI := moduleFinite hp H
  exact Module.free_of_finite_type_torsion_free'

theorem linearIndependent_qb {ι : Type} (b : ι → B) (hb : LinearIndependent (Rp p) b) :
    LinearIndependent Qb (fun i => (b i : X → Qb)) := by
  haveI := GaloisRep.isFractionRing_ratLocalizedAt p
  have h1 : LinearIndependent (Rp p) (fun i => (b i : X → Qb)) :=
    hb.map' B.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have h2 : LinearIndependent ℚ (fun i => (b i : X → Qb)) :=
    (LinearIndependent.iff_fractionRing (Rp p) ℚ).mp h1
  letI : MulAction Γℚ X := inferInstance
  exact AlgebraicClosure.linearIndependent_of_linearIndependent_rat_of_forall_apply_smul _
    (fun i σ x => H.equiv _ (b i).2 σ x) h2

theorem restrict_qb {ι : Type} {v : ι → X × X → Qb} (h : LinearIndependent Qb v) :
    LinearIndependent (Rp p) v :=
  letI : SMulWithZero (Rp p) Qb := (Module.toMulActionWithZero (R := Rp p) (M := Qb)).toSMulWithZero
  h.restrict_scalars (by
    intro r s hrs
    apply algebraMap_injective (p := p)
    simp only [Algebra.smul_def, mul_one] at hrs
    exact hrs)

theorem restrict_qb₃ {ι : Type} {v : ι → X × (X × X) → Qb} (h : LinearIndependent Qb v) :
    LinearIndependent (Rp p) v :=
  letI : SMulWithZero (Rp p) Qb := (Module.toMulActionWithZero (R := Rp p) (M := Qb)).toSMulWithZero
  h.restrict_scalars (by
    intro r s hrs
    apply algebraMap_injective (p := p)
    simp only [Algebra.smul_def, mul_one] at hrs
    exact hrs)

theorem θ₂_injective : Function.Injective (θ₂ B) := by
  haveI := moduleFree hp H
  haveI := moduleFinite hp H
  let b := Module.Free.chooseBasis (Rp p) B
  have hb := linearIndependent_qb hp H b b.linearIndependent
  have h2 := linearIndependent_mul _ _ hb hb
  refine injective_of_linearIndependent_basis (R := Rp p) (V := B ⊗[Rp p] B) (W := X × X → Qb)
    (b.tensorProduct b) (θ₂ B).toLinearMap ?_
  convert restrict_qb hp H h2 using 1
  all_goals try rfl
  funext ij
  rw [Module.Basis.tensorProduct_apply']
  rfl

theorem θ₃_injective : Function.Injective (θ₃ B) := by
  haveI := moduleFree hp H
  haveI := moduleFinite hp H
  let b := Module.Free.chooseBasis (Rp p) B
  have hb := linearIndependent_qb hp H b b.linearIndependent
  have h2 := linearIndependent_mul _ _ hb (linearIndependent_mul _ _ hb hb)
  refine injective_of_linearIndependent_basis (R := Rp p) (V := B ⊗[Rp p] (B ⊗[Rp p] B))
    (W := X × (X × X) → Qb) (b.tensorProduct (b.tensorProduct b)) (θ₃ B).toLinearMap ?_
  convert restrict_qb₃ hp H h2 using 1
  all_goals try rfl
  funext ijk
  rw [Module.Basis.tensorProduct_apply', Module.Basis.tensorProduct_apply']
  rfl

variable (B) in

def mstar : B →ₐ[Rp p] (X × X → Qb) := incl B (fun xy => xy.1 + xy.2)

omit hp H in
theorem mstar_apply (F : B) (xy : X × X) : mstar B F xy = (F : X → Qb) (xy.1 + xy.2) := rfl

theorem mstar_mem_range (F : B) : mstar B F ∈ LinearMap.range (θ₂ B).toLinearMap := by
  obtain ⟨n, F₁, F₂, h₁, h₂, hlaw⟩ := H.comul F F.2
  refine ⟨∑ i, (⟨F₁ i, h₁ i⟩ : B) ⊗ₜ (⟨F₂ i, h₂ i⟩ : B), ?_⟩
  funext xy
  rw [AlgHom.toLinearMap_apply, map_sum, Finset.sum_apply, mstar_apply, hlaw]
  rfl

def comulLin : B →ₗ[Rp p] B ⊗[Rp p] B :=
  (LinearEquiv.ofInjective (θ₂ B).toLinearMap (θ₂_injective hp H)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (θ₂ B).toLinearMap) (mstar B).toLinearMap
      (mstar_mem_range hp H)

theorem θ₂_comulLin (F : B) : θ₂ B (comulLin hp H F) = mstar B F := by
  have h1 := LinearEquiv.ofInjective_apply (θ₂ B).toLinearMap (h := θ₂_injective hp H)
    ((LinearEquiv.ofInjective (θ₂ B).toLinearMap (θ₂_injective hp H)).symm
      ⟨mstar B F, mstar_mem_range hp H F⟩)
  rw [LinearEquiv.apply_symm_apply] at h1
  exact h1.symm

theorem θ₂_comulLin_apply (F : B) (xy : X × X) :
    θ₂ B (comulLin hp H F) xy = (F : X → Qb) (xy.1 + xy.2) := by
  rw [θ₂_comulLin]; rfl

theorem comulLin_eq_sum (F : B) {n : ℕ} (F₁ F₂ : Fin n → B)
    (hlaw : ∀ x y : X, (F : X → Qb) (x + y) = ∑ i, (F₁ i : X → Qb) x * (F₂ i : X → Qb) y) :
    comulLin hp H F = ∑ i, F₁ i ⊗ₜ F₂ i := by
  apply θ₂_injective hp H
  funext xy
  rw [θ₂_comulLin_apply, hlaw, map_sum, Finset.sum_apply]
  rfl

theorem exists_law (F : B) : ∃ (n : ℕ) (F₁ F₂ : Fin n → B),
    ∀ x y : X, (F : X → Qb) (x + y) = ∑ i, (F₁ i : X → Qb) x * (F₂ i : X → Qb) y := by
  obtain ⟨n, F₁, F₂, h₁, h₂, hlaw⟩ := H.comul F F.2
  exact ⟨n, fun i => ⟨F₁ i, h₁ i⟩, fun i => ⟨F₂ i, h₂ i⟩, hlaw⟩

theorem apply_zero_mem_range (F : B) : (F : X → Qb) 0 ∈ Set.range (algebraMap (Rp p) Qb) := by
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp
  haveI := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI := moduleFinite hp H

  have hfix : ∀ σ : Γℚ, σ ((F : X → Qb) 0) = (F : X → Qb) 0 := fun σ => by
    rw [← H.equiv _ F.2 σ 0, smul_zero]
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp ((InfiniteGalois.mem_bot_iff_fixed _).mpr hfix)

  haveI : Algebra.IsIntegral (Rp p) B := Algebra.IsIntegral.of_finite (Rp p) B
  have hint : IsIntegral (Rp p) ((F : X → Qb) 0) :=
    (Algebra.IsIntegral.isIntegral F).map ((Pi.evalAlgHom (Rp p) (fun _ : X => Qb) 0).comp B.val)
  rw [← hq] at hint
  have hint' : IsIntegral (Rp p) q :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (Rp p) ℚ Qb) (algebraMap ℚ Qb).injective).mp hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  refine ⟨r, ?_⟩
  rw [← hq, ← hr, IsScalarTower.algebraMap_apply (Rp p) ℚ Qb]

def counitFun (F : B) : Rp p := Classical.choose (apply_zero_mem_range hp H F)

theorem algebraMap_counitFun (F : B) : algebraMap (Rp p) Qb (counitFun hp H F) = (F : X → Qb) 0 :=
  Classical.choose_spec (apply_zero_mem_range hp H F)

def counitAlg : B →ₐ[Rp p] Rp p where
  toFun := counitFun hp H
  map_one' := algebraMap_injective (by rw [algebraMap_counitFun, map_one]; rfl)
  map_mul' F F' := algebraMap_injective (by
    rw [algebraMap_counitFun, map_mul, algebraMap_counitFun, algebraMap_counitFun]; rfl)
  map_zero' := algebraMap_injective (by rw [algebraMap_counitFun, map_zero]; rfl)
  map_add' F F' := algebraMap_injective (by
    rw [algebraMap_counitFun, map_add, algebraMap_counitFun, algebraMap_counitFun]; rfl)
  commutes' r := algebraMap_injective (by rw [algebraMap_counitFun]; rfl)

theorem algebraMap_counitAlg (F : B) : algebraMap (Rp p) Qb (counitAlg hp H F) = (F : X → Qb) 0 :=
  algebraMap_counitFun hp H F

omit hp H in
theorem θ₃_assoc_tmul (T : B ⊗[Rp p] B) (G : B) (t : X × (X × X)) :
    θ₃ B (TensorProduct.assoc (Rp p) B B B (T ⊗ₜ G)) t = θ₂ B T (t.1, t.2.1) * (G : X → Qb) t.2.2 := by
  induction T using TensorProduct.induction_on with
  | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply,
      zero_mul]
  | tmul a b => rw [TensorProduct.assoc_tmul, θ₃_tmul, θ₂_tmul, θ₂_tmul, mul_assoc]
  | add a b ha hb => rw [TensorProduct.add_tmul, map_add, map_add, Pi.add_apply, ha, hb, map_add,
      Pi.add_apply, add_mul]

theorem coassoc_lhs (F : B) (t : X × (X × X)) :
    θ₃ B (TensorProduct.assoc (Rp p) B B B
      (LinearMap.rTensor B (comulLin hp H) (comulLin hp H F))) t =
      (F : X → Qb) ((t.1 + t.2.1) + t.2.2) := by
  obtain ⟨n, F₁, F₂, hlaw⟩ := exists_law hp H F
  rw [comulLin_eq_sum hp H F F₁ F₂ hlaw, map_sum, map_sum, map_sum, Finset.sum_apply, hlaw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.rTensor_tmul, θ₃_assoc_tmul, θ₂_comulLin_apply]

theorem coassoc_rhs (F : B) (t : X × (X × X)) :
    θ₃ B (LinearMap.lTensor B (comulLin hp H) (comulLin hp H F)) t =
      (F : X → Qb) (t.1 + (t.2.1 + t.2.2)) := by
  obtain ⟨n, F₁, F₂, hlaw⟩ := exists_law hp H F
  rw [comulLin_eq_sum hp H F F₁ F₂ hlaw, map_sum, map_sum, Finset.sum_apply, hlaw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.lTensor_tmul, θ₃_tmul, θ₂_comulLin_apply]

theorem counit_left (F : B) (y : X) :
    ((TensorProduct.lid (Rp p) B (LinearMap.rTensor B (counitAlg hp H).toLinearMap
      (comulLin hp H F)) : B) : X → Qb) y = (F : X → Qb) y := by
  obtain ⟨n, F₁, F₂, hlaw⟩ := exists_law hp H F
  rw [comulLin_eq_sum hp H F F₁ F₂ hlaw, map_sum, map_sum, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_apply, ← zero_add y, hlaw, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, Subalgebra.coe_smul]
  change counitAlg hp H (F₁ i) • ((F₂ i : X → Qb) y) = _
  rw [subring_smul_eq, algebraMap_counitAlg]

theorem counit_right (F : B) (x : X) :
    ((TensorProduct.rid (Rp p) B (LinearMap.lTensor B (counitAlg hp H).toLinearMap
      (comulLin hp H F)) : B) : X → Qb) x = (F : X → Qb) x := by
  obtain ⟨n, F₁, F₂, hlaw⟩ := exists_law hp H F
  rw [comulLin_eq_sum hp H F F₁ F₂ hlaw, map_sum, map_sum, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_apply, ← add_zero x, hlaw, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, AlgHom.toLinearMap_apply, Subalgebra.coe_smul]
  change counitAlg hp H (F₂ i) • ((F₁ i : X → Qb) x) = _
  rw [subring_smul_eq, algebraMap_counitAlg, mul_comm]

@[reducible] def coalgebra : Coalgebra (Rp p) B where
  comul := comulLin hp H
  counit := (counitAlg hp H).toLinearMap
  coassoc := by
    apply LinearMap.ext
    intro F
    apply θ₃_injective hp H
    funext t
    change θ₃ B (TensorProduct.assoc (Rp p) B B B
      (LinearMap.rTensor B (comulLin hp H) (comulLin hp H F))) t =
      θ₃ B (LinearMap.lTensor B (comulLin hp H) (comulLin hp H F)) t
    rw [coassoc_lhs, coassoc_rhs, add_assoc]
  rTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro F
    apply (TensorProduct.lid (Rp p) B).injective
    apply Subtype.val_injective
    funext y
    change ((TensorProduct.lid (Rp p) B (LinearMap.rTensor B (counitAlg hp H).toLinearMap
      (comulLin hp H F)) : B) : X → Qb) y = ((TensorProduct.lid (Rp p) B ((1 : Rp p) ⊗ₜ F) : B) : X → Qb) y
    rw [counit_left, TensorProduct.lid_tmul, one_smul]
  lTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro F
    apply (TensorProduct.rid (Rp p) B).injective
    apply Subtype.val_injective
    funext x
    change ((TensorProduct.rid (Rp p) B (LinearMap.lTensor B (counitAlg hp H).toLinearMap
      (comulLin hp H F)) : B) : X → Qb) x = ((TensorProduct.rid (Rp p) B (F ⊗ₜ (1 : Rp p)) : B) : X → Qb) x
    rw [counit_right, TensorProduct.rid_tmul, one_smul]

@[reducible] def bialgebra : Bialgebra (Rp p) B :=
  @Bialgebra.mk' (Rp p) B _ _ _ (coalgebra hp H)
    (by
      apply algebraMap_injective (p := p)
      change algebraMap (Rp p) Qb (counitAlg hp H 1) = _
      rw [algebraMap_counitAlg, map_one]; rfl)
    (fun {a b} => by
      apply algebraMap_injective (p := p)
      change algebraMap (Rp p) Qb (counitAlg hp H (a * b)) =
        algebraMap (Rp p) Qb (counitAlg hp H a * counitAlg hp H b)
      rw [algebraMap_counitAlg, map_mul, algebraMap_counitAlg, algebraMap_counitAlg]; rfl)
    (by
      apply θ₂_injective hp H
      change θ₂ B (comulLin hp H 1) = θ₂ B 1
      funext xy
      rw [θ₂_comulLin_apply, map_one]; rfl)
    (fun {a b} => by
      apply θ₂_injective hp H
      change θ₂ B (comulLin hp H (a * b)) = θ₂ B (comulLin hp H a * comulLin hp H b)
      funext xy
      rw [θ₂_comulLin_apply, map_mul (θ₂ B), Pi.mul_apply, θ₂_comulLin_apply, θ₂_comulLin_apply]
      rfl)

def antipodeLin : B →ₗ[Rp p] B where
  toFun F := ⟨fun x => (F : X → Qb) (-x), H.neg _ F.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_antipodeLin (F : B) (x : X) : (antipodeLin H F : X → Qb) x = (F : X → Qb) (-x) := rfl

theorem antipode_left (F : B) (y : X) :
    ((LinearMap.mul' (Rp p) B (LinearMap.rTensor B (antipodeLin H) (comulLin hp H F)) : B) :
      X → Qb) y = (F : X → Qb) 0 := by
  obtain ⟨n, F₁, F₂, hlaw⟩ := exists_law hp H F
  rw [comulLin_eq_sum hp H F F₁ F₂ hlaw, map_sum, map_sum, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_apply, ← neg_add_cancel y, hlaw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.rTensor_tmul, LinearMap.mul'_apply]
  rfl

theorem antipode_right (F : B) (y : X) :
    ((LinearMap.mul' (Rp p) B (LinearMap.lTensor B (antipodeLin H) (comulLin hp H F)) : B) :
      X → Qb) y = (F : X → Qb) 0 := by
  obtain ⟨n, F₁, F₂, hlaw⟩ := exists_law hp H F
  rw [comulLin_eq_sum hp H F F₁ F₂ hlaw, map_sum, map_sum, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_apply, ← add_neg_cancel y, hlaw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.lTensor_tmul, LinearMap.mul'_apply]
  rfl

@[reducible] def hopfAlgebra : HopfAlgebra (Rp p) B :=
  { bialgebra hp H with
    antipode := antipodeLin H
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext
      intro F
      apply Subtype.val_injective
      funext y
      change ((LinearMap.mul' (Rp p) B (LinearMap.rTensor B (antipodeLin H) (comulLin hp H F)) :
        B) : X → Qb) y = ((algebraMap (Rp p) B (counitAlg hp H F) : B) : X → Qb) y
      rw [antipode_left, Subalgebra.coe_algebraMap]
      change _ = algebraMap (Rp p) Qb (counitAlg hp H F)
      rw [algebraMap_counitAlg]
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext
      intro F
      apply Subtype.val_injective
      funext y
      change ((LinearMap.mul' (Rp p) B (LinearMap.lTensor B (antipodeLin H) (comulLin hp H F)) :
        B) : X → Qb) y = ((algebraMap (Rp p) B (counitAlg hp H F) : B) : X → Qb) y
      rw [antipode_right, Subalgebra.coe_algebraMap]
      change _ = algebraMap (Rp p) Qb (counitAlg hp H F)
      rw [algebraMap_counitAlg] }

omit hp H in
theorem θ₂_comm (T : B ⊗[Rp p] B) (xy : X × X) :
    θ₂ B (TensorProduct.comm (Rp p) B B T) xy = θ₂ B T xy.swap := by
  induction T using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | tmul a b => rw [TensorProduct.comm_tmul, θ₂_tmul, θ₂_tmul, Prod.fst_swap, Prod.snd_swap, mul_comm]
  | add a b ha hb => rw [map_add, map_add, Pi.add_apply, ha, hb, map_add, Pi.add_apply]

theorem isCocomm : @Coalgebra.IsCocomm (Rp p) B _ _ _ (coalgebra hp H) := by
  refine @Coalgebra.IsCocomm.mk (Rp p) B _ _ _ (coalgebra hp H) ?_
  apply LinearMap.ext
  intro F
  apply θ₂_injective hp H
  funext xy
  change θ₂ B (TensorProduct.comm (Rp p) B B (comulLin hp H F)) xy = θ₂ B (comulLin hp H F) xy
  rw [θ₂_comm, θ₂_comulLin_apply, θ₂_comulLin_apply, Prod.fst_swap, Prod.snd_swap, add_comm]

theorem moduleFlat : Module.Flat (Rp p) B := by
  haveI := moduleFree hp H
  infer_instance

variable (B) in

def evalPt (x : X) : B →ₐ[Rp p] Qb := (Pi.evalAlgHom (Rp p) (fun _ : X => Qb) x).comp B.val

omit hp H in
theorem evalPt_apply (x : X) (F : B) : evalPt B x F = (F : X → Qb) x := rfl

theorem evalPt_injective : Function.Injective (evalPt B) := by
  intro x y hxy
  exact H.sep x y fun F hF => by
    have := DFunLike.congr_fun hxy ⟨F, hF⟩
    exact this

variable (B) in

def ΦQ : Qb ⊗[Rp p] B →ₐ[Qb] (X → Qb) :=
  Algebra.TensorProduct.lift (Algebra.ofId Qb (X → Qb)) B.val fun _ _ => Commute.all _ _

omit hp H in
theorem ΦQ_tmul (c : Qb) (F : B) : ΦQ B (c ⊗ₜ F) = algebraMap Qb (X → Qb) c * (F : X → Qb) :=
  Algebra.TensorProduct.lift_tmul _ _ _ c F

theorem ΦQ_injective : Function.Injective (ΦQ B) := by
  haveI := moduleFree hp H
  haveI := moduleFinite hp H
  let b := Module.Free.chooseBasis (Rp p) B
  have hb := linearIndependent_qb hp H b b.linearIndependent
  refine injective_of_linearIndependent_basis (Algebra.TensorProduct.basis Qb b) (ΦQ B).toLinearMap ?_
  convert hb using 1
  all_goals try rfl
  funext i
  rw [Algebra.TensorProduct.basis_apply, AlgHom.toLinearMap_apply, ΦQ_tmul, map_one, one_mul]

theorem single_mem_range [DecidableEq X] (x : X) : (Pi.single x (1 : Qb) : X → Qb) ∈ (ΦQ B).range := by
  haveI := Fintype.ofFinite X

  have hsepF : ∀ y : X, y ≠ x → ∃ F ∈ B, F x ≠ F y := by
    intro y hy
    by_contra h
    push Not at h
    exact hy (H.sep y x fun F hF => (h F hF).symm)
  choose! Fs hFsB hFs using hsepF
  have hmemF : ∀ y, y ≠ x → (Fs y : X → Qb) ∈ (ΦQ B).range := fun y hy =>
    ⟨(1 : Qb) ⊗ₜ ⟨Fs y, hFsB y hy⟩, by
      change ΦQ B ((1 : Qb) ⊗ₜ ⟨Fs y, hFsB y hy⟩) = Fs y
      rw [ΦQ_tmul, map_one, one_mul]⟩

  let fac : X → X → Qb := fun y =>
    algebraMap Qb (X → Qb) ((Fs y x - Fs y y)⁻¹) * (Fs y - algebraMap Qb (X → Qb) (Fs y y))
  have hfac_mem : ∀ y, y ≠ x → fac y ∈ (ΦQ B).range := fun y hy =>
    Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sub_mem _ (hmemF y hy) (Subalgebra.algebraMap_mem _ _))
  have hfac_x : ∀ y, y ≠ x → fac y x = 1 := by
    intro y hy
    change (Fs y x - Fs y y)⁻¹ * (Fs y x - Fs y y) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hFs y hy))
  have hfac_y : ∀ y, y ≠ x → fac y y = 0 := by
    intro y hy
    change (Fs y x - Fs y y)⁻¹ * (Fs y y - Fs y y) = 0
    rw [sub_self, mul_zero]
  have hprod : (∏ y ∈ Finset.univ.filter (· ≠ x), fac y) = Pi.single x (1 : Qb) := by
    funext z
    rw [Finset.prod_apply]
    by_cases hz : z = x
    · rw [hz, Pi.single_eq_same]
      exact Finset.prod_eq_one fun y hy => hfac_x y (Finset.mem_filter.mp hy).2
    · rw [Pi.single_eq_of_ne hz]
      exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩) (hfac_y z hz)
  rw [← hprod]
  exact Subalgebra.prod_mem _ fun y hy => hfac_mem y (Finset.mem_filter.mp hy).2

theorem ΦQ_surjective : Function.Surjective (ΦQ B) := by
  classical
  haveI := Fintype.ofFinite X
  intro f
  suffices h : f ∈ (ΦQ B).range from h
  induction f using Pi.single_induction with
  | zero => exact Subalgebra.zero_mem _
  | add f g hf hg => exact Subalgebra.add_mem _ hf hg
  | single x c =>
    have h1 : (Pi.single x c : X → Qb) = c • Pi.single x (1 : Qb) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [h1]
    exact Subalgebra.smul_mem _ (single_mem_range hp H x) c

theorem exists_eq_eval (ψ : (X → Qb) →ₐ[Qb] Qb) : ∃ x₀ : X, ∀ f : X → Qb, ψ f = f x₀ := by
  classical
  haveI := Fintype.ofFinite X
  let e : X → Qb := fun x => ψ (Pi.single x 1)
  have hmul : ∀ x y : X, e x * e y = if x = y then e x else 0 := by
    intro x y
    change ψ _ * ψ _ = _
    rw [← map_mul]
    have h1 : (Pi.single x (1 : Qb) * Pi.single y 1 : X → Qb) = if x = y then Pi.single x 1 else 0 := by
      funext z
      rw [Pi.mul_apply]
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl]
        by_cases hz : z = x
        · subst hz; simp
        · simp [Pi.single_eq_of_ne hz]
      · rw [if_neg hxy, Pi.zero_apply]
        by_cases hz : z = x
        · subst hz; simp [Pi.single_eq_of_ne hxy]
        · simp [Pi.single_eq_of_ne hz]
    rw [h1]
    split_ifs <;> simp [e]
  have hsum : ∑ x, e x = 1 := by
    change ∑ x, ψ _ = 1
    rw [← map_sum, Finset.univ_sum_single (fun _ : X => (1 : Qb))]
    exact map_one ψ

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, e x₀ ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero fun x _ => h x] at hsum
    exact zero_ne_one hsum
  have hidem : e x₀ * e x₀ = e x₀ := by rw [hmul, if_pos rfl]
  have hone : e x₀ = 1 := by
    have h2 : e x₀ * (e x₀ - 1) = 0 := by rw [mul_sub, hidem, mul_one, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hx₀
    · exact sub_eq_zero.mp h3
  have hother : ∀ x, x ≠ x₀ → e x = 0 := by
    intro x hx
    have h3 := hmul x x₀
    rw [if_neg hx, hone, mul_one] at h3
    exact h3
  refine ⟨x₀, fun f => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single f]
  rw [map_sum]
  have h4 : ∀ x, ψ (Pi.single x (f x)) = f x * e x := by
    intro x
    have h5 : (Pi.single x (f x) : X → Qb) = f x • Pi.single x (1 : Qb) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [h5, map_smul, smul_eq_mul]
  simp_rw [h4]
  rw [Finset.sum_eq_single x₀ (fun x _ hx => by rw [hother x hx, mul_zero])
    (fun h => absurd (Finset.mem_univ x₀) h), hone, mul_one]

theorem evalPt_surjective : Function.Surjective (evalPt B) := by
  intro π
  let Φe : Qb ⊗[Rp p] B ≃ₐ[Qb] (X → Qb) :=
    AlgEquiv.ofBijective (ΦQ B) ⟨ΦQ_injective hp H, ΦQ_surjective hp H⟩
  let πt : Qb ⊗[Rp p] B →ₐ[Qb] Qb :=
    Algebra.TensorProduct.lift (AlgHom.id Qb Qb) π fun _ _ => Commute.all _ _
  obtain ⟨x₀, hx₀⟩ := exists_eq_eval hp H (πt.comp (Φe.symm : (X → Qb) →ₐ[Qb] Qb ⊗[Rp p] B))
  refine ⟨x₀, AlgHom.ext fun F => ?_⟩
  have h1 : π F = πt ((1 : Qb) ⊗ₜ F) := by
    change π F = AlgHom.id Qb Qb 1 * π F
    rw [map_one, one_mul]
  have h2 : ((1 : Qb) ⊗ₜ F : Qb ⊗[Rp p] B) = Φe.symm (F : X → Qb) := by
    apply Φe.injective
    rw [AlgEquiv.apply_symm_apply]
    change ΦQ B ((1 : Qb) ⊗ₜ F) = _
    rw [ΦQ_tmul, map_one, one_mul]
  rw [evalPt_apply, h1, h2]
  exact (hx₀ (F : X → Qb)).symm

theorem conv_evalPt (x y : X) :
    letI := bialgebra hp H
    WithConv.toConv (evalPt B x) * WithConv.toConv (evalPt B y) =
      WithConv.toConv (evalPt B (x + y)) := by
  letI := bialgebra hp H
  apply WithConv.ext
  apply AlgHom.toLinearMap_injective
  have h2 := congrArg WithConv.ofConv
    (AlgHom.toLinearMap_convMul (WithConv.toConv (evalPt B x)) (WithConv.toConv (evalPt B y)))
  change (WithConv.toConv (evalPt B x) * WithConv.toConv (evalPt B y)).ofConv.toLinearMap = _ at h2
  rw [h2]
  apply LinearMap.ext
  intro F
  obtain ⟨n, F₁, F₂, hlaw⟩ := exists_law hp H F
  let 𝓡 : Coalgebra.Repr (Rp p) F _ :=
    { index := Finset.univ, left := F₁, right := F₂, eq := (comulLin_eq_sum hp H F F₁ F₂ hlaw).symm }
  rw [𝓡.convMul_apply]
  change ∑ i, (F₁ i : X → Qb) x * (F₂ i : X → Qb) y = (F : X → Qb) (x + y)
  rw [hlaw]

end setting

end P2mHopfOrder
p2m_reactivate "P2MW.S_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure.P2mHopfOrder"

open P2mHopfOrder in
theorem solution (p : ℕ) (hp : p.Prime)
    {X : Type} [AddCommGroup X] [Finite X]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X]
    (B : Subalgebra (GaloisRep.ratLocalizedAt p) (X → AlgebraicClosure ℚ))
    (hfin : (Subalgebra.toSubmodule B).FG)
    (hequiv : ∀ F ∈ B, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X),
      F (σ • x) = σ (F x))
    (hcomul : ∀ F ∈ B, ∃ (n : ℕ) (F₁ F₂ : Fin n → X → AlgebraicClosure ℚ),
      (∀ i, F₁ i ∈ B) ∧ (∀ i, F₂ i ∈ B) ∧ ∀ x y : X, F (x + y) = ∑ i, F₁ i x * F₂ i y)
    (hneg : ∀ F ∈ B, (fun x => F (-x)) ∈ B)
    (hsep : ∀ x y : X, (∀ F ∈ B, F x = F y) → x = y) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ X,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e g = σ • (e f) := by
  have HH : IsHopfOrder B := ⟨hfin, hequiv, hcomul, hneg, hsep⟩
  letI hB : HopfAlgebra (Rp p) B := hopfAlgebra hp HH
  refine ⟨B, inferInstance, hB, moduleFinite hp HH, moduleFlat hp HH, isCocomm hp HH, ?_⟩
  have hbij : Function.Bijective (fun x : X => WithConv.toConv (evalPt B x)) := by
    refine ⟨fun x y h => evalPt_injective hp HH (WithConv.toConv_injective h), fun f => ?_⟩
    obtain ⟨x, hx⟩ := evalPt_surjective hp HH f.ofConv
    exact ⟨x, by change WithConv.toConv (evalPt B x) = f; rw [hx]⟩
  set E := Equiv.ofBijective _ hbij with hE
  refine ⟨E.symm, fun f g => ?_, fun σ f g hfg => ?_⟩
  · obtain ⟨x, rfl⟩ := E.surjective f
    obtain ⟨y, rfl⟩ := E.surjective g
    have h1 : E x * E y = E (x + y) := conv_evalPt hp HH x y
    rw [h1, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · obtain ⟨x, rfl⟩ := E.surjective f
    have h1 : g = E (σ • x) := by
      apply WithConv.ext
      apply AlgHom.ext
      intro F
      rw [hfg F]
      change σ ((F : X → AlgebraicClosure ℚ) x) = (F : X → AlgebraicClosure ℚ) (σ • x)
      exact (hequiv _ F.2 σ x).symm
    rw [h1, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end
p2m_reactivate "P2MW.S_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure.P2mHopfOrder"

end S_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure
end P2MW
export P2MW.S_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure (solution)
