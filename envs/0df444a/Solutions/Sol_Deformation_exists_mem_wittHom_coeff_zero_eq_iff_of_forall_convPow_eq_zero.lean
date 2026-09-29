-- Prove2me | solution 1 for Deformation.exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8e09626a-bcd5-5134-bd0d-1fa7e34971ce

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_HopfTower
import Theorems.Thm_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero
import Theorems.Thm_Deformation_convPow_prime_apply_coeff_of_mem_wittHom
import Theorems.Thm_Deformation_mem_wittHom_one_iff_coeff_mem_primitives
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open Function CartierDual

universe u v

namespace Deformation
p2m_export "Deformation" "wittHom wittHomMap coeff_wittHomMap truncateLE_mem_wittHom exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero convPow_prime_apply_coeff_of_mem_wittHom mem_wittHom_one_iff_coeff_mem_primitives"
namespace WittFirstCoord
p2m_open "Deformation"

section Bridges

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

theorem toDual_pow (φ : CartierDual k A) (m : ℕ) :
    CartierDual.toDual k A (φ ^ m) = (WithConv.toConv (CartierDual.toDual k A φ) ^ m).ofConv := by
  induction m with
  | zero =>
    refine LinearMap.ext fun a => ?_
    rw [pow_zero, pow_zero, LinearMap.convOne_apply, Algebra.algebraMap_self_apply]
    exact CartierDual.one_apply a
  | succ m ih =>
    rw [pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv, ← pow_succ]

theorem convPow_apply (β : WithConv (A →ₗ[k] k)) (m : ℕ) (x : A) :
    (β ^ m).ofConv x = ((CartierDual.ofDual k A β.ofConv) ^ m) x := by
  have : (β ^ m).ofConv = CartierDual.toDual k A ((CartierDual.ofDual k A β.ofConv) ^ m) := by
    rw [toDual_pow, CartierDual.toDual_ofDual, WithConv.toConv_ofConv]
  rw [this]; rfl

theorem ofDual_pow_eq_zero {β : WithConv (A →ₗ[k] k)} {m : ℕ} (h : β ^ m = 0) :
    (CartierDual.ofDual k A β.ofConv) ^ m = 0 := by
  refine CartierDual.ext fun x => ?_
  rw [← convPow_apply, h]
  rfl

theorem convPow_eq_zero {φ : CartierDual k A} {m : ℕ} (h : φ ^ m = 0) :
    (WithConv.toConv (CartierDual.toDual k A φ)) ^ m = 0 := by
  have : (WithConv.toConv (CartierDual.toDual k A φ) ^ m).ofConv = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [convPow_apply, WithConv.ofConv_toConv, CartierDual.ofDual_toDual, h]
    rfl
  exact (WithConv.ofConv_injective this : _)

theorem mul_apply_one (φ ψ : CartierDual k A) : (φ * ψ) 1 = φ 1 * ψ 1 := by
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply]
  rfl

theorem pow_apply_one (φ : CartierDual k A) (m : ℕ) : (φ ^ m) 1 = (φ 1) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, CartierDual.one_apply, Bialgebra.counit_one]
  | succ m ih => rw [pow_succ, mul_apply_one, ih, pow_succ]

theorem smul_apply' (c : k) (φ : CartierDual k A) (x : A) : (c • φ) x = c * φ x := rfl

theorem add_apply' (φ ψ : CartierDual k A) (x : A) : (φ + ψ) x = φ x + ψ x := rfl

theorem sub_apply' (φ ψ : CartierDual k A) (x : A) : (φ - ψ) x = φ x - ψ x := rfl

theorem zero_apply' (x : A) : (0 : CartierDual k A) x = 0 := rfl

theorem algebraMap_injective : Injective (algebraMap k (CartierDual k A)) := by
  intro r s h
  have := congrArg (fun φ : CartierDual k A => φ 1) h
  simpa only [CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul] using this

scoped instance instCharP : CharP (CartierDual k A) p :=
  charP_of_injective_algebraMap algebraMap_injective p

theorem antipode_pow (φ : CartierDual k A) (m : ℕ) :
    HopfAlgebra.antipode k (A := CartierDual k A) (φ ^ m) =
      (HopfAlgebra.antipode k (A := CartierDual k A) φ) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, HopfAlgebra.antipode_one]
  | succ m ih => rw [pow_succ, HopfAlgebra.antipode_mul, ih, ← pow_succ']

theorem tmul_ext {z : A ⊗[k] A}
    (h : ∀ φ ψ : Module.Dual k A, TensorProduct.dualDistrib k A A (φ ⊗ₜ[k] ψ) z = 0) : z = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro F
  obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k A A).surjective F
  change TensorProduct.dualDistrib k A A w z = 0
  induction w with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | tmul φ ψ => exact h φ ψ

theorem dualDistrib_eq_apply_rid_lTensor (θ ψ : Module.Dual k A) (z : A ⊗[k] A) :
    TensorProduct.dualDistrib k A A (θ ⊗ₜ[k] ψ) z =
      θ (TensorProduct.rid k A (LinearMap.lTensor A ψ z)) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [TensorProduct.dualDistrib_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul,
      smul_eq_mul, mul_comm]

theorem dualDistrib_eq_apply_lid_rTensor (θ ψ : Module.Dual k A) (z : A ⊗[k] A) :
    TensorProduct.dualDistrib k A A (θ ⊗ₜ[k] ψ) z =
      ψ (TensorProduct.lid k A (LinearMap.rTensor A θ z)) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [TensorProduct.dualDistrib_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul,
      smul_eq_mul]

end Bridges

section RangeLemma

variable {k : Type u} [Field k]
variable {A : Type v} [AddCommGroup A] [Module k A] [Module.Finite k A]

theorem tmul_ext' {z : A ⊗[k] A}
    (h : ∀ φ ψ : Module.Dual k A, TensorProduct.dualDistrib k A A (φ ⊗ₜ[k] ψ) z = 0) : z = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro F
  obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k A A).surjective F
  change TensorProduct.dualDistrib k A A w z = 0
  induction w with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | tmul φ ψ => exact h φ ψ

theorem dualDistrib_rTensor (θ ψ : Module.Dual k A) (q : A →ₗ[k] A) (z : A ⊗[k] A) :
    TensorProduct.dualDistrib k A A (θ ⊗ₜ[k] ψ) (LinearMap.rTensor A q z) =
      TensorProduct.dualDistrib k A A ((θ ∘ₗ q) ⊗ₜ[k] ψ) z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp

theorem dualDistrib_lTensor (θ ψ : Module.Dual k A) (q : A →ₗ[k] A) (z : A ⊗[k] A) :
    TensorProduct.dualDistrib k A A (θ ⊗ₜ[k] ψ) (LinearMap.lTensor A q z) =
      TensorProduct.dualDistrib k A A (θ ⊗ₜ[k] (ψ ∘ₗ q)) z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp

theorem dualDistrib_eq_apply_rid_lTensor' (θ ψ : Module.Dual k A) (z : A ⊗[k] A) :
    TensorProduct.dualDistrib k A A (θ ⊗ₜ[k] ψ) z =
      θ (TensorProduct.rid k A (LinearMap.lTensor A ψ z)) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [TensorProduct.dualDistrib_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul,
      smul_eq_mul, mul_comm]

theorem dualDistrib_eq_apply_lid_rTensor' (θ ψ : Module.Dual k A) (z : A ⊗[k] A) :
    TensorProduct.dualDistrib k A A (θ ⊗ₜ[k] ψ) z =
      ψ (TensorProduct.lid k A (LinearMap.rTensor A θ z)) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [TensorProduct.dualDistrib_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul,
      smul_eq_mul]

theorem mem_range_map_subtype_of_forall_dual (W : Submodule k A) {z : A ⊗[k] A}
    (h1 : ∀ ψ : Module.Dual k A, TensorProduct.rid k A (LinearMap.lTensor A ψ z) ∈ W)
    (h2 : ∀ θ : Module.Dual k A, TensorProduct.lid k A (LinearMap.rTensor A θ z) ∈ W) :
    z ∈ LinearMap.range (TensorProduct.map W.subtype W.subtype) := by
  obtain ⟨W', hc⟩ := Submodule.exists_isCompl W

  set q : A →ₗ[k] A := W.projection W' hc with hq
  set q' : A →ₗ[k] A := W'.projection W hc.symm with hq'
  have hqq' : q + q' = LinearMap.id := Submodule.projection_add_projection_eq_id hc
  have hq'W : ∀ w ∈ W, q' w = 0 := fun w hw => by
    have h := Submodule.projectionOnto_apply_right hc.symm ⟨w, hw⟩
    rw [hq', Submodule.projection_apply]
    exact congrArg Subtype.val h

  have hA : LinearMap.rTensor A q' z = 0 := by
    refine tmul_ext' fun θ ψ => ?_
    rw [dualDistrib_rTensor, dualDistrib_eq_apply_rid_lTensor', LinearMap.comp_apply, hq'W _ (h1 ψ),
      map_zero]
  have hB : LinearMap.lTensor A q' z = 0 := by
    refine tmul_ext' fun θ ψ => ?_
    rw [dualDistrib_lTensor, dualDistrib_eq_apply_lid_rTensor', LinearMap.comp_apply, hq'W _ (h2 θ),
      map_zero]
  have hz : z = TensorProduct.map q q z := by
    conv_lhs => rw [← LinearMap.id_apply (R := k) z, ← TensorProduct.map_id, ← hqq']
    rw [TensorProduct.map_add_left, TensorProduct.map_add_right, TensorProduct.map_add_right,
      LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply]
    have e1 : TensorProduct.map q q' z = 0 := by
      rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hB, map_zero]
    have e2 : TensorProduct.map q' q z = 0 := by
      rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hA, map_zero]
    have e3 : TensorProduct.map q' q' z = 0 := by
      rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hB, map_zero]
    rw [e1, e2, e3, add_zero, add_zero, add_zero]
  refine ⟨TensorProduct.map (W.projectionOnto W' hc) (W.projectionOnto W' hc) z, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  exact hz.symm

end RangeLemma

section AnnV

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
variable (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

def annVSub : Submodule k A where
  carrier := {a | ∀ φ : CartierDual k A, φ ^ p = 0 → φ a = 0}
  add_mem' {a b} ha hb φ hφ := by rw [map_add, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' φ _ := map_zero φ
  smul_mem' c {a} ha φ hφ := by rw [map_smul, ha φ hφ, smul_zero]

variable {k p A}

theorem mem_annVSub_iff {a : A} : a ∈ annVSub k p A ↔ ∀ φ : CartierDual k A, φ ^ p = 0 → φ a = 0 :=
  Iff.rfl

theorem one_mem_annVSub : (1 : A) ∈ annVSub k p A := fun φ hφ => by
  have h : (φ 1) ^ p = 0 := by rw [← pow_apply_one, hφ]; rfl
  exact pow_eq_zero_iff hp.out.ne_zero |>.1 h

section Witness

variable [PerfectField k]

theorem pow_apply_eq_of_pow_eq {a : A} (ha : a ∈ annVSub k p A) {φ ψ : CartierDual k A}
    (h : φ ^ p = ψ ^ p) : (φ a) ^ p = (ψ a) ^ p := by
  have h1 : (φ - ψ) ^ p = 0 := by rw [sub_pow_char, h, sub_self]
  have h2 : (φ - ψ) a = 0 := ha _ h1
  rw [sub_apply', sub_eq_zero] at h2
  rw [h2]

variable (k p A) in

def frobIm : Submodule k (CartierDual k A) where
  carrier := {r | ∃ φ : CartierDual k A, φ ^ p = r}
  add_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨φ + ψ, add_pow_char _ _ _⟩
  zero_mem' := ⟨0, zero_pow hp.out.ne_zero⟩
  smul_mem' c := by
    rintro _ ⟨φ, rfl⟩
    refine ⟨(frobeniusEquiv k p).symm c • φ, ?_⟩
    rw [smul_pow, frobeniusEquiv_symm_pow_p]

def witnessFun (a : A) (r : frobIm k p A) : k := ((Classical.choose r.2) a) ^ p

theorem witnessFun_eq {a : A} (ha : a ∈ annVSub k p A) (φ : CartierDual k A)
    (r : frobIm k p A) (hr : φ ^ p = (r : CartierDual k A)) : witnessFun a r = (φ a) ^ p := by
  have hc : (Classical.choose r.2) ^ p = (r : CartierDual k A) := Classical.choose_spec r.2
  exact pow_apply_eq_of_pow_eq ha (hc.trans hr.symm)

def witnessLin {a : A} (ha : a ∈ annVSub k p A) : frobIm k p A →ₗ[k] k where
  toFun := witnessFun a
  map_add' r s := by
    obtain ⟨φ, hφ⟩ := r.2
    obtain ⟨ψ, hψ⟩ := s.2
    have hrs : (φ + ψ) ^ p = ((r + s : frobIm k p A) : CartierDual k A) := by
      rw [add_pow_char, hφ, hψ]; rfl
    rw [witnessFun_eq ha φ r hφ, witnessFun_eq ha ψ s hψ, witnessFun_eq ha (φ + ψ) (r + s) hrs,
      add_apply', add_pow_char]
  map_smul' c r := by
    obtain ⟨φ, hφ⟩ := r.2
    have hcr : ((frobeniusEquiv k p).symm c • φ) ^ p = ((c • r : frobIm k p A) : CartierDual k A) := by
      rw [smul_pow, frobeniusEquiv_symm_pow_p, hφ]; rfl
    rw [witnessFun_eq ha φ r hφ, witnessFun_eq ha _ (c • r) hcr, smul_apply', mul_pow,
      RingHom.id_apply, smul_eq_mul, frobeniusEquiv_symm_pow_p]

theorem exists_witness {a : A} (ha : a ∈ annVSub k p A) :
    ∃ a' : A, ∀ φ : CartierDual k A, (φ a) ^ p = (φ ^ p) a' := by
  obtain ⟨G, hG⟩ := LinearMap.exists_extend (witnessLin ha)
  refine ⟨(Module.evalEquiv k A).symm (G ∘ₗ (CartierDual.ofDual k A).toLinearMap), fun φ => ?_⟩
  have h1 := Module.apply_evalEquiv_symm_apply k A (CartierDual.toDual k A (φ ^ p))
    (G ∘ₗ (CartierDual.ofDual k A).toLinearMap)
  rw [CartierDual.toDual_apply] at h1
  rw [h1, LinearMap.comp_apply]
  have h2 : G (φ ^ p) = witnessLin ha ⟨φ ^ p, φ, rfl⟩ := by
    rw [← hG]; rfl
  change (φ a) ^ p = G (φ ^ p)
  rw [h2]
  exact (witnessFun_eq ha φ ⟨φ ^ p, φ, rfl⟩ rfl).symm

end Witness

def pair₂ (a b : A) : CartierDual k A ⊗[k] CartierDual k A →ₗ[k] k :=
  (TensorProduct.dualDistrib k A A ∘ₗ
    TensorProduct.map (CartierDual.toDual k A).toLinearMap (CartierDual.toDual k A).toLinearMap).flip
    (a ⊗ₜ[k] b)

theorem pair₂_apply (a b : A) (w : CartierDual k A ⊗[k] CartierDual k A) :
    pair₂ a b w = TensorProduct.dualDistrib k A A
      (TensorProduct.map (CartierDual.toDual k A).toLinearMap (CartierDual.toDual k A).toLinearMap w)
      (a ⊗ₜ[k] b) := rfl

theorem pair₂_tmul (a b : A) (φ ψ : CartierDual k A) : pair₂ a b (φ ⊗ₜ[k] ψ) = φ a * ψ b := by
  rw [pair₂_apply, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]; rfl

theorem pair₂_comul (a b : A) (φ : CartierDual k A) :
    pair₂ a b (Coalgebra.comul (R := k) φ) = φ (a * b) := by
  rw [pair₂_apply]
  exact CartierDual.comul_pairing φ a b

scoped instance instNontrivialTensor : Nontrivial (CartierDual k A ⊗[k] CartierDual k A) :=
  RingHom.domain_nontrivial
    (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (CartierDual k A))
      (Bialgebra.counitAlgHom k (CartierDual k A)) (fun _ _ => Commute.all _ _)).toRingHom

scoped instance instCharPTensor : CharP (CartierDual k A ⊗[k] CartierDual k A) p :=
  charP_of_injective_algebraMap (algebraMap k (CartierDual k A ⊗[k] CartierDual k A)).injective p

open Coalgebra in

theorem pair₂_comul_pow_of_witness {a b a' b' : A}
    (ha : ∀ φ : CartierDual k A, (φ a) ^ p = (φ ^ p) a')
    (hb : ∀ φ : CartierDual k A, (φ b) ^ p = (φ ^ p) b') (φ : CartierDual k A) :
    (pair₂ a b (Coalgebra.comul (R := k) φ)) ^ p = pair₂ a' b' (Coalgebra.comul (R := k) (φ ^ p)) := by
  have hcomul : Coalgebra.comul (R := k) (φ ^ p) = (Coalgebra.comul (R := k) φ) ^ p := by
    have := map_pow (Bialgebra.comulAlgHom k (CartierDual k A)) φ p
    simpa only [Bialgebra.comulAlgHom_apply] using this
  have hfd := sum_pow_char p (ℛ k φ).index (fun i => (ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i)
  have hfd' : (∑ i ∈ (ℛ k φ).index, (ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i) ^ p =
      ∑ i ∈ (ℛ k φ).index, ((ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i) ^ p := hfd
  rw [hcomul, ← (ℛ k φ).eq, hfd', map_sum, map_sum]
  have hk := sum_pow_char p (ℛ k φ).index (fun i => pair₂ a b ((ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i))
  have hk' : (∑ i ∈ (ℛ k φ).index, pair₂ a b ((ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i)) ^ p =
      ∑ i ∈ (ℛ k φ).index, (pair₂ a b ((ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i)) ^ p := hk
  rw [hk']
  refine Finset.sum_congr rfl fun i _ => ?_
  have htp : ((ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i) ^ p =
      ((ℛ k φ).left i ^ p) ⊗ₜ[k] ((ℛ k φ).right i ^ p) := Algebra.TensorProduct.tmul_pow _ _ _
  rw [htp, pair₂_tmul, pair₂_tmul, mul_pow, ha, hb]

variable [PerfectField k]

theorem mul_mem_annVSub {a b : A} (ha : a ∈ annVSub k p A) (hb : b ∈ annVSub k p A) :
    a * b ∈ annVSub k p A := by
  obtain ⟨a', ha'⟩ := exists_witness ha
  obtain ⟨b', hb'⟩ := exists_witness hb
  intro φ hφ
  have h : (φ (a * b)) ^ p = 0 := by
    rw [← pair₂_comul, pair₂_comul_pow_of_witness ha' hb', hφ, pair₂_comul, zero_apply']
  exact pow_eq_zero_iff hp.out.ne_zero |>.1 h

variable (k p A)

def annV : Subalgebra k A where
  carrier := annVSub k p A
  mul_mem' ha hb := mul_mem_annVSub ha hb
  one_mem' := one_mem_annVSub
  add_mem' ha hb := (annVSub k p A).add_mem ha hb
  zero_mem' := (annVSub k p A).zero_mem
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (annVSub k p A).smul_mem c one_mem_annVSub

variable {k p A}

theorem mem_annV_iff {a : A} : a ∈ annV k p A ↔ ∀ φ : CartierDual k A, φ ^ p = 0 → φ a = 0 :=
  Iff.rfl

theorem annV_toSubmodule : (annV k p A).toSubmodule = annVSub k p A := rfl

theorem rid_lTensor_comul_mem {a : A} (ha : a ∈ annV k p A) (ψ : Module.Dual k A) :
    TensorProduct.rid k A (LinearMap.lTensor A ψ (Coalgebra.comul (R := k) a)) ∈ annV k p A := by
  intro φ hφ
  have h := dualDistrib_eq_apply_rid_lTensor (CartierDual.toDual k A φ) ψ (Coalgebra.comul (R := k) a)
  rw [CartierDual.toDual_apply] at h
  rw [← h]
  have hm := CartierDual.mul_apply φ (CartierDual.ofDual k A ψ) a
  rw [CartierDual.toDual_ofDual] at hm
  rw [← hm]
  refine ha _ ?_
  rw [mul_pow, hφ, zero_mul]

theorem lid_rTensor_comul_mem {a : A} (ha : a ∈ annV k p A) (θ : Module.Dual k A) :
    TensorProduct.lid k A (LinearMap.rTensor A θ (Coalgebra.comul (R := k) a)) ∈ annV k p A := by
  intro φ hφ
  have h := dualDistrib_eq_apply_lid_rTensor θ (CartierDual.toDual k A φ) (Coalgebra.comul (R := k) a)
  rw [CartierDual.toDual_apply] at h
  rw [← h]
  have hm := CartierDual.mul_apply (CartierDual.ofDual k A θ) φ a
  rw [CartierDual.toDual_ofDual] at hm
  rw [← hm]
  refine ha _ ?_
  rw [mul_pow, hφ, mul_zero]

theorem comul_mem_range {a : A} (ha : a ∈ annV k p A) :
    Coalgebra.comul (R := k) a ∈
      LinearMap.range (TensorProduct.map (annV k p A).val.toLinearMap (annV k p A).val.toLinearMap) :=
  mem_range_map_subtype_of_forall_dual (annV k p A).toSubmodule (rid_lTensor_comul_mem ha)
    (lid_rTensor_comul_mem ha)

theorem antipode_mem_annV {a : A} (ha : a ∈ annV k p A) :
    HopfAlgebra.antipode k a ∈ annV k p A := by
  intro φ hφ
  rw [← CartierDual.antipode_apply]
  refine ha _ ?_
  rw [← antipode_pow, hφ, LinearMap.map_zero]

theorem isHopfSubalgebra_annV : HopfAlgebra.IsHopfSubalgebra k (annV k p A) where
  comul_mem a ha := by
    rw [← HopfAlgebra.IsHopfSubalgebra.range_ι₂, HopfAlgebra.IsHopfSubalgebra.ι₂_eq_map]
    exact comul_mem_range ha
  antipode_mem a ha := antipode_mem_annV ha

end AnnV

section AnnVHopf

variable {k : Type u} [Field k] [PerfectField k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

scoped instance instHopfAlgebraAnnV : HopfAlgebra k ↥(annV k p A) :=
  (isHopfSubalgebra_annV (k := k) (p := p) (A := A)).hopfAlgebra

scoped instance instModuleFiniteAnnV : Module.Finite k ↥(annV k p A) :=
  Module.Finite.of_injective (annV k p A).val.toLinearMap Subtype.val_injective

scoped instance instIsCocommAnnV : Coalgebra.IsCocomm k ↥(annV k p A) where
  comm_comp_comul := by
    ext s
    apply HopfAlgebra.IsHopfSubalgebra.ι₂_injective (K := annV k p A)
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, HopfAlgebra.IsHopfSubalgebra.ι₂_eq_map,
      HopfAlgebra.HopfKerHopf.map_comm, ← HopfAlgebra.IsHopfSubalgebra.ι₂_eq_map,
      (isHopfSubalgebra_annV (k := k) (p := p) (A := A)).ι₂_comul, Coalgebra.comm_comul]

scoped instance instIsHopfTowerAnnV : HopfAlgebra.IsHopfTower k ↥(annV k p A) A :=
  (isHopfSubalgebra_annV (k := k) (p := p) (A := A)).isHopfTower

variable (k p A) in

def incl : ↥(annV k p A) →ₐc[k] A := HopfAlgebra.IsHopfTower.toBialgHom k ↥(annV k p A) A

@[scoped simp] theorem incl_apply (s : ↥(annV k p A)) : incl k p A s = (s : A) := rfl

variable (k p A) in

def res : CartierDual k A →ₐ[k] CartierDual k ↥(annV k p A) := CartierDual.mapAlgHom (incl k p A)

@[scoped simp] theorem res_apply (φ : CartierDual k A) (s : ↥(annV k p A)) : res k p A φ s = φ (s : A) := rfl

theorem res_surjective : Surjective (res k p A) := by
  intro φ'
  obtain ⟨G, hG⟩ := LinearMap.exists_extend (p := (annV k p A).toSubmodule) (CartierDual.toDual k _ φ')
  refine ⟨CartierDual.ofDual k A G, CartierDual.ext fun s => ?_⟩
  rw [res_apply, CartierDual.ofDual_apply]
  have := LinearMap.congr_fun hG s
  exact this

theorem res_eq_zero_of_forall {χ : CartierDual k A} (h : ∀ a ∈ annV k p A, χ a = 0) :
    res k p A χ = 0 :=
  CartierDual.ext fun s => h _ s.2

variable (k p A) in

def frobKer : Submodule k (Module.Dual k A) where
  carrier := {f | (CartierDual.ofDual k A f) ^ p = 0}
  add_mem' {f g} hf hg := by
    change (CartierDual.ofDual k A f + CartierDual.ofDual k A g) ^ p = 0
    rw [add_pow_char, hf, hg, add_zero]
  zero_mem' := zero_pow hp.out.ne_zero
  smul_mem' c f hf := by
    change (c • CartierDual.ofDual k A f) ^ p = 0
    rw [smul_pow, hf, smul_zero]

theorem dualCoannihilator_frobKer : (frobKer k p A).dualCoannihilator = (annV k p A).toSubmodule := by
  ext a
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h φ hφ
    exact h (CartierDual.toDual k A φ) hφ
  · intro h f hf
    exact h (CartierDual.ofDual k A f) hf

theorem pow_prime_eq_zero_of_forall_annV {χ : CartierDual k A} (h : ∀ a ∈ annV k p A, χ a = 0) :
    χ ^ p = 0 := by
  have hmem : CartierDual.toDual k A χ ∈ ((annV k p A).toSubmodule).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    exact fun a ha => h a ha
  rw [← dualCoannihilator_frobKer, Subspace.dualCoannihilator_dualAnnihilator_eq] at hmem
  exact hmem

end AnnVHopf

section Induction

variable (k : Type u) [Field k] [PerfectField k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

def IND (n : ℕ) : Prop :=
  ∀ (B : Type v) [CommRing B] [HopfAlgebra k B] [Module.Finite k B] [Coalgebra.IsCocomm k B],
    (∀ φ : CartierDual k B, φ 1 = 0 → φ ^ p ^ (n + 1) = 0) →
    ∀ x₀ : B, x₀ ∈ primitives k B → (∀ φ : CartierDual k B, φ ^ p ^ n = 0 → φ x₀ = 0) →
      ∃ x : TruncatedWittVector p (n + 1) B, x ∈ Deformation.wittHom k p (n + 1) B ∧ x.coeff 0 = x₀

theorem IND_zero : IND.{u, v} k p 0 := by
  intro B _ _ _ _ _ x₀ hx₀ _
  refine ⟨TruncatedWittVector.mk p fun _ => x₀, ?_, TruncatedWittVector.coeff_mk _ _⟩
  rw [Deformation.mem_wittHom_one_iff_coeff_mem_primitives k p B, TruncatedWittVector.coeff_mk]
  exact hx₀

theorem IND_succ (n : ℕ) (ih : IND.{u, v} k p n) : IND.{u, v} k p (n + 1) := by
  intro B _ _ _ _ hV x₀ hx₀ hann
  have hp0 : p ≠ 0 := hp.out.ne_zero

  have hx₀K : x₀ ∈ annV k p B := fun φ hφ =>
    hann φ (by rw [pow_succ', pow_mul, hφ, zero_pow (pow_ne_zero _ hp0)])
  set x₀' : ↥(annV k p B) := ⟨x₀, hx₀K⟩ with hx₀'

  have hV' : ∀ φ' : CartierDual k ↥(annV k p B), φ' 1 = 0 → φ' ^ p ^ (n + 1) = 0 := by
    intro φ' h1
    obtain ⟨φ, rfl⟩ := res_surjective φ'
    have hφ1 : φ 1 = 0 := h1
    rw [← map_pow]
    refine res_eq_zero_of_forall fun a ha => ha _ ?_
    have := hV φ hφ1
    rwa [pow_succ, pow_mul] at this

  have hann' : ∀ φ' : CartierDual k ↥(annV k p B), φ' ^ p ^ n = 0 → φ' x₀' = 0 := by
    intro φ' h
    obtain ⟨φ, rfl⟩ := res_surjective φ'
    rw [← map_pow] at h
    have hk : ∀ a ∈ annV k p B, (φ ^ p ^ n) a = 0 := fun a ha =>
      congrArg (fun ψ : CartierDual k ↥(annV k p B) => ψ ⟨a, ha⟩) h
    have h2 := pow_prime_eq_zero_of_forall_annV hk
    rw [← pow_mul, ← pow_succ] at h2
    exact hann φ h2

  have hprim' : x₀' ∈ primitives k ↥(annV k p B) := by
    change Coalgebra.comul (R := k) x₀' - x₀' ⊗ₜ[k] (1 : ↥(annV k p B)) - (1 : ↥(annV k p B)) ⊗ₜ[k] x₀'
      = 0
    apply HopfAlgebra.IsHopfSubalgebra.ι₂_injective (K := annV k p B)
    rw [map_zero, map_sub, map_sub, (isHopfSubalgebra_annV (k := k) (p := p) (A := B)).ι₂_comul,
      HopfAlgebra.IsHopfSubalgebra.ι₂_tmul, HopfAlgebra.IsHopfSubalgebra.ι₂_tmul]
    exact hx₀
  obtain ⟨xb, hxb, hxb0⟩ := ih ↥(annV k p B) hV' x₀' hprim' hann'

  set x'' : Deformation.wittHom k p (n + 1) B := Deformation.wittHomMap p (n + 1) (incl k p B) ⟨xb, hxb⟩
    with hx''
  have hcoe : ∀ i, (x'' : TruncatedWittVector p (n + 1) B).coeff i = ((xb.coeff i : ↥(annV k p B)) : B) :=
    fun i => Deformation.coeff_wittHomMap _ _ i

  obtain ⟨y, hy, hyt⟩ :=
    Deformation.exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero k p n B
      (x'' : TruncatedWittVector p (n + 1) B) x''.2 (fun β hβ => by
        rw [hcoe]
        exact (xb.coeff (Fin.last n)).2 (CartierDual.ofDual k B β.ofConv) (ofDual_pow_eq_zero hβ))
  refine ⟨y, hy, ?_⟩
  have h0 := TruncatedWittVector.coeff_truncate (Nat.le_succ (n + 1)) 0 y
  rw [hyt, hcoe, hxb0] at h0
  exact h0.symm

theorem IND_all (n : ℕ) : IND.{u, v} k p n := by
  induction n with
  | zero => exact IND_zero k p
  | succ n ih => exact IND_succ k p n ih

end Induction

section Forward

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {A : Type v} [CommRing A] [HopfAlgebra k A]

theorem convPow_pow_apply_coeff {n : ℕ} {x : TruncatedWittVector p n A}
    (hx : x ∈ Deformation.wittHom k p n A) (β : WithConv (A →ₗ[k] k)) :
    ∀ (j : ℕ) (hj : j < n), (β ^ p ^ j).ofConv (x.coeff ⟨j, hj⟩) =
      (β.ofConv (x.coeff ⟨0, lt_of_le_of_lt (Nat.zero_le j) hj⟩)) ^ p ^ j := by
  intro j
  induction j with
  | zero => intro hj; rw [pow_zero, pow_one, pow_one]
  | succ j ih =>
    intro hj
    have h := (Deformation.convPow_prime_apply_coeff_of_mem_wittHom k p A k (β ^ p ^ j) hx).2 j hj
    rw [← pow_mul, ← pow_succ] at h
    rw [h, ih (Nat.lt_of_succ_lt hj), ← pow_mul, ← pow_succ]

end Forward

end Deformation.WittFirstCoord
p2m_reactivate "P2MW.S_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero.Deformation P2MW.S_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero.Deformation.WittFirstCoord"
p2m_reactivate "P2MW.S_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero.Deformation"

open Deformation.WittFirstCoord in

theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ (n + 1) = 0)
    (x₀ : A) :
    (∃ x : TruncatedWittVector p (n + 1) A,
        x ∈ Deformation.wittHom k p (n + 1) A ∧ x.coeff 0 = x₀) ↔
      (x₀ ∈ primitives k A ∧
        ∃ a : A, ∀ β : WithConv (A →ₗ[k] k),
          (β.ofConv x₀) ^ p ^ n = (β ^ p ^ n).ofConv a) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, x.coeff (Fin.last n), fun β => ?_⟩
    · have h1 := Deformation.truncateLE_mem_wittHom (Nat.succ_le_succ (Nat.zero_le n)) hx
      have h2 := (Deformation.mem_wittHom_one_iff_coeff_mem_primitives k p A _).1 h1
      rwa [TruncatedWittVector.coeff_truncate] at h2
    · exact (convPow_pow_apply_coeff hx β n (Nat.lt_succ_self n)).symm
  · rintro ⟨hprim, a, ha⟩
    have hV' : ∀ φ : CartierDual k A, φ 1 = 0 → φ ^ p ^ (n + 1) = 0 := fun φ hφ =>
      ofDual_pow_eq_zero (hV (WithConv.toConv (CartierDual.toDual k A φ)) hφ)
    have hann : ∀ φ : CartierDual k A, φ ^ p ^ n = 0 → φ x₀ = 0 := by
      intro φ hφ
      have h := ha (WithConv.toConv (CartierDual.toDual k A φ))
      rw [convPow_apply, WithConv.ofConv_toConv, CartierDual.ofDual_toDual, hφ, zero_apply'] at h
      exact pow_eq_zero_iff (pow_ne_zero n hp0) |>.1 h
    exact IND_all k p n A hV' x₀ hprim hann

end
end S_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero
end P2MW
export P2MW.S_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero (solution)
