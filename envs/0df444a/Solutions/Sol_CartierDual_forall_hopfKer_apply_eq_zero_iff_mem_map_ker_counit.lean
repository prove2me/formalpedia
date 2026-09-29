-- Prove2me | solution 1 for CartierDual.forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d56567ea-318e-5312-baff-36ebfbc5c07a

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit

set_option autoImplicit false

universe u v w

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace CartierExact

variable {R : Type u} [CommRing R]

theorem dualDistrib_tmul_comp {M N N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N']
    (ψ : Module.Dual R M) (χ : Module.Dual R N') (g : N →ₗ[R] N') (z : M ⊗[R] N) :
    TensorProduct.dualDistrib R M N (ψ ⊗ₜ[R] (χ ∘ₗ g)) z =
      TensorProduct.dualDistrib R M N' (ψ ⊗ₜ[R] χ) (g.lTensor M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [TensorProduct.dualDistrib_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem dualDistrib_map_dualMap {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (g : N →ₗ[R] N)
    (w : Module.Dual R M ⊗[R] Module.Dual R N) (z : M ⊗[R] N) :
    TensorProduct.dualDistrib R M N (TensorProduct.map LinearMap.id g.dualMap w) z =
      TensorProduct.dualDistrib R M N w (g.lTensor M z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul ψ χ =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.dualMap_apply']
    exact dualDistrib_tmul_comp ψ χ g z
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

variable {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
  [Coalgebra.IsCocomm R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
  [Coalgebra.IsCocomm R B]

variable (π : A →ₐc[R] B)

omit [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] [Module.Finite R B]
  [Module.Free R B] [Coalgebra.IsCocomm R B] in
theorem coaction_eq_lTensor (a : A) :
    coaction π a = (π : A →ₐc[R] B).toLinearMap.lTensor A (comul (R := R) a) :=
  HopfKerHopf.coaction_eq_map π a

omit [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] [Module.Finite R B]
  [Module.Free R B] [Coalgebra.IsCocomm R B] in

theorem pi_eq_of_mem {c : A} (hc : c ∈ hopfKer π) : π c = algebraMap R B (counit (R := R) c) := by
  have h := coaction_eq_of_mem π hc
  rw [coaction_eq_lTensor] at h
  have key := congrArg (fun z => TensorProduct.lid R B ((counit (R := R) (A := A)).rTensor B z)) h
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul,
    LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, one_smul] at key
  rw [Algebra.algebraMap_eq_smul_one]
  exact key

omit [Module.Finite R A] [Coalgebra.IsCocomm R A] [Module.Finite R B] [Module.Free R B]
  [Coalgebra.IsCocomm R B] in

theorem exists_lTensor_val_eq_comul {c : A} (hc : c ∈ hopfKer π) :
    ∃ w : A ⊗[R] ↥(hopfKer π), (HopfKerHopf.valL π).lTensor A w = comul (R := R) c := by
  have ex : Function.Exact ((HopfKerHopf.valL π).lTensor A) ((HopfKerHopf.rhoSub π).lTensor A) :=
    Module.Flat.lTensor_exact A (HopfKerHopf.exact_valL_rhoSub π)
  exact (ex _).mp (HopfKerHopf.lTensor_rhoSub_comul π hc)

theorem apply_eq_zero_of_mem (φ : CartierDual R A)
    (hφ : φ ∈ Ideal.map (CartierDual.map π)
      (RingHom.ker (Bialgebra.counitAlgHom R (CartierDual R B)))) :
    ∀ c ∈ hopfKer π, φ c = 0 := by
  rw [Ideal.map] at hφ
  refine Submodule.span_induction (p := fun θ _ => ∀ c ∈ hopfKer π, θ c = 0) ?_ ?_ ?_ ?_ hφ
  · rintro θ ⟨χ, hχ, rfl⟩ c hc
    have hχ1 : χ 1 = 0 := by
      have h := hχ
      rw [SetLike.mem_coe, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at h
      erw [CartierDual.counit_apply] at h
      exact h
    rw [CartierDual.map_apply, pi_eq_of_mem π hc, Algebra.algebraMap_eq_smul_one, map_smul, hχ1,
      smul_zero]
  · intro c _; rfl
  · intro x y _ _ hx hy c hc
    change x c + y c = 0
    rw [hx c hc, hy c hc, add_zero]
  · intro θ' θ _ hθ c hc
    change (θ' * θ) c = 0
    obtain ⟨w, hw⟩ := exists_lTensor_val_eq_comul π hc
    rw [CartierDual.mul_apply, ← hw]
    have hθ0 : (CartierDual.toDual R A θ) ∘ₗ HopfKerHopf.valL π = 0 := by
      refine LinearMap.ext fun s => ?_
      exact hθ s s.2
    rw [← dualDistrib_tmul_comp, hθ0, TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply]

variable (hπ : Function.Surjective π)

def Θ : Module.Dual R A ⊗[R] Module.Dual R B →ₗ[R] CartierDual R A :=
  TensorProduct.lift
    (LinearMap.mk₂ R
      (fun ψ χ => CartierDual.ofDual R A ψ * CartierDual.map π (CartierDual.ofDual R B χ))
      (fun ψ ψ' χ => by simp only [map_add, add_mul])
      (fun t ψ χ => by simp only [map_smul, smul_mul_assoc])
      (fun ψ χ χ' => by simp only [map_add, mul_add])
      (fun t ψ χ => by simp only [map_smul, mul_smul_comm]))

theorem Θ_tmul (ψ : Module.Dual R A) (χ : Module.Dual R B) :
    Θ π (ψ ⊗ₜ[R] χ) = CartierDual.ofDual R A ψ * CartierDual.map π (CartierDual.ofDual R B χ) :=
  rfl

theorem Θ_apply (w : Module.Dual R A ⊗[R] Module.Dual R B) (a : A) :
    Θ π w a = TensorProduct.dualDistrib R A B w (coaction π a) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]; rfl
  | tmul ψ χ =>
    rw [Θ_tmul, CartierDual.mul_apply, CartierDual.toDual_ofDual, CartierDual.toDual_map,
      CartierDual.toDual_ofDual, LinearMap.dualMap_apply', coaction_eq_lTensor]
    exact dualDistrib_tmul_comp ψ χ _ _
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, ← hx, ← hy]
    rfl

def prB : B →ₗ[R] B := LinearMap.id - (Algebra.linearMap R B) ∘ₗ counit

omit [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R B] [Module.Free R B] [Coalgebra.IsCocomm R B] in
theorem prB_apply (b : B) : prB (R := R) b = b - algebraMap R B (counit (R := R) b) := rfl

omit [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R B] [Module.Free R B] [Coalgebra.IsCocomm R B] in
theorem prB_one : prB (R := R) (1 : B) = 0 := by
  rw [prB_apply, counit_one, map_one, sub_self]

theorem Θ_mem (w' : Module.Dual R A ⊗[R] Module.Dual R B) :
    Θ π (TensorProduct.map LinearMap.id (prB (R := R) (B := B)).dualMap w') ∈
      Ideal.map (CartierDual.map π) (RingHom.ker (Bialgebra.counitAlgHom R (CartierDual R B))) := by
  induction w' using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Ideal.zero_mem _
  | tmul ψ χ =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, Θ_tmul]
    refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
    erw [CartierDual.counit_apply]
    rw [CartierDual.ofDual_apply, LinearMap.dualMap_apply', LinearMap.comp_apply, prB_one, map_zero]
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Ideal.add_mem _ hx hy

omit [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] [Module.Finite R B]
  [Module.Free R B] [Coalgebra.IsCocomm R B] in

theorem lTensor_prB_coaction (a : A) :
    (prB (R := R) (B := B)).lTensor A (coaction π a) = coaction π a - a ⊗ₜ[R] 1 := by
  rw [prB, LinearMap.lTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_id, LinearMap.id_apply]
  congr 1
  rw [coaction_eq_lTensor, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.comp_assoc]
  have hc : counit ∘ₗ (π : A →ₐc[R] B).toLinearMap = counit := CoalgHomClass.counit_comp π
  rw [hc, LinearMap.lTensor_comp, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul,
    LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]

include hπ in
theorem mem_of_apply_eq_zero (φ : CartierDual R A) (hφ : ∀ c ∈ hopfKer π, φ c = 0) :
    φ ∈ Ideal.map (CartierDual.map π)
      (RingHom.ker (Bialgebra.counitAlgHom R (CartierDual R B))) := by
  obtain ⟨⟨r, hr⟩, -, -, -⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  have hGal := HopfAlgebra.isHopfGalois_of_surjective π hπ
  let CM : Submodule R A := Subalgebra.toSubmodule (hopfKer π)

  let rR : A →ₗ[R] A := (hopfKer π).val.toLinearMap ∘ₗ (r.restrictScalars R)
  have rR_apply : ∀ a, rR a = (r a : A) := fun a => rfl
  have rR_mul : ∀ (a : A) {h : A} (hh : h ∈ hopfKer π), rR (a * h) = h * rR a := by
    intro a h hh
    rw [rR_apply, rR_apply, mul_comm a h, show h * a = (⟨h, hh⟩ : ↥(hopfKer π)) • a from rfl,
      LinearMap.map_smul]
    rfl

  let ρ₀ : A ⊗[R] A →ₗ[R] A ⧸ CM :=
    TensorProduct.lift (((LinearMap.mul R A).comp rR).compr₂ CM.mkQ)
  have ρ₀_tmul : ∀ a a' : A, ρ₀ (a ⊗ₜ[R] a') = CM.mkQ (rR a * a') := fun a a' => rfl

  have hbal : balancingRelations π ⊆ (LinearMap.ker ρ₀ : Set (A ⊗[R] A)) := by
    rintro x ⟨a, h, a', hh, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, ρ₀_tmul, ρ₀_tmul, rR_mul a hh, sub_eq_zero,
      mul_assoc, mul_left_comm]
  have hker : LinearMap.ker (canMap π) ≤ LinearMap.ker ρ₀ := by
    intro z hz
    have hz' : z ∈ Submodule.span R (balancingRelations π) := hGal.2 z hz
    exact (Submodule.span_le.2 hbal) hz'
  let ρt : A ⊗[R] B →ₗ[R] A ⧸ CM :=
    ((LinearMap.ker (canMap π)).liftQ ρ₀ hker).comp
      (LinearMap.quotKerEquivOfSurjective (canMap π) hGal.1).symm.toLinearMap
  have ρt_canMap : ∀ z, ρt (canMap π z) = ρ₀ z := by
    intro z
    change (LinearMap.ker (canMap π)).liftQ ρ₀ hker
      ((LinearMap.quotKerEquivOfSurjective (canMap π) hGal.1).symm (canMap π z)) = ρ₀ z
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have ρt_key : ∀ a : A, ρt (coaction π a - a ⊗ₜ[R] 1) = CM.mkQ a := by
    intro a
    rw [map_sub, ← canMap_one_tmul, ← canMap_tmul_one π a, ρt_canMap, ρt_canMap, ρ₀_tmul,
      ρ₀_tmul, mul_one]
    have h1 : rR 1 = 1 := by
      rw [rR_apply, show (1 : A) = ((1 : ↥(hopfKer π)) : A) from rfl, hr]
    have h2 : CM.mkQ (rR a) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact (r a).2
    rw [h1, one_mul, h2, sub_zero]

  have hφ' : CM ≤ LinearMap.ker (CartierDual.toDual R A φ) := fun c hc => hφ c hc
  let φbar : (A ⧸ CM) →ₗ[R] R := CM.liftQ (CartierDual.toDual R A φ) hφ'
  let Fl : Module.Dual R (A ⊗[R] B) := φbar ∘ₗ ρt
  have Fl_key : ∀ a : A, Fl (coaction π a - a ⊗ₜ[R] 1) = φ a := by
    intro a
    change φbar (ρt (coaction π a - a ⊗ₜ[R] 1)) = φ a
    rw [ρt_key, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl

  let w' : Module.Dual R A ⊗[R] Module.Dual R B := (TensorProduct.dualDistribEquiv R A B).symm Fl
  have hw' : TensorProduct.dualDistrib R A B w' = Fl := by
    change TensorProduct.dualDistribEquiv R A B ((TensorProduct.dualDistribEquiv R A B).symm Fl) = Fl
    exact LinearEquiv.apply_symm_apply _ _

  have hφeq : φ = Θ π (TensorProduct.map LinearMap.id (prB (R := R) (B := B)).dualMap w') := by
    refine CartierDual.ext fun a => ?_
    rw [Θ_apply, dualDistrib_map_dualMap, hw', lTensor_prB_coaction, Fl_key]
  rw [hφeq]
  exact Θ_mem π w'

include hπ in
theorem main (φ : CartierDual R A) :
    (∀ a ∈ hopfKer π, φ a = 0) ↔
      φ ∈ Ideal.map (CartierDual.map π)
        (RingHom.ker (Bialgebra.counitAlgHom R (CartierDual R B))) :=
  ⟨mem_of_apply_eq_zero π hπ φ, apply_eq_zero_of_mem π φ⟩

end CartierExact

end

theorem solution
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
    [Coalgebra.IsCocomm R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    [Coalgebra.IsCocomm R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) (φ : CartierDual R A) :
    (∀ a ∈ HopfAlgebra.hopfKer π, φ a = 0) ↔
      φ ∈ Ideal.map (CartierDual.map π)
        (RingHom.ker (Bialgebra.counitAlgHom R (CartierDual R B))) :=
  CartierExact.main π hπ φ

end S_CartierDual_forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit
end P2MW
export P2MW.S_CartierDual_forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit (solution)
