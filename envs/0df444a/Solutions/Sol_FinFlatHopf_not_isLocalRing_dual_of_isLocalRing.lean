-- Prove2me | solution 1 for FinFlatHopf.not_isLocalRing_dual_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/48866e28-dd7b-556c-a6e5-0cfb12c5540b

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.RingTheory.OrzechProperty
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Theorems.Thm_FinFlatHopf_exists_left_integral_frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FinFlatHopf_not_isLocalRing_dual_of_isLocalRing

set_option Elab.async false

noncomputable section

open Coalgebra HopfAlgebra WithConv
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

namespace FinFlatHopf
p2m_export "FinFlatHopf" "exists_left_integral_frobenius"
p2m_open "FinFlatHopf"

variable {B : Type} [CommRing B] {H : Type} [CommRing H] [HopfAlgebra B H]

theorem sum_coassoc {M : Type*} [AddCommMonoid M] [Module B M]
    (ψ : H ⊗[B] (H ⊗[B] H) →ₗ[B] M) {a : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr B a ι𝓡)
    {κ₁ κ₂ : ι𝓡 → Type*}
    (𝓡₁ : ∀ i, Coalgebra.Repr B (𝓡.left i) (κ₁ i)) (𝓡₂ : ∀ i, Coalgebra.Repr B (𝓡.right i) (κ₂ i)) :
    ∑ i ∈ 𝓡.index, ∑ j ∈ (𝓡₁ i).index,
        ψ ((𝓡₁ i).left j ⊗ₜ[B] ((𝓡₁ i).right j ⊗ₜ[B] 𝓡.right i)) =
      ∑ i ∈ 𝓡.index, ∑ j ∈ (𝓡₂ i).index,
        ψ (𝓡.left i ⊗ₜ[B] ((𝓡₂ i).left j ⊗ₜ[B] (𝓡₂ i).right j)) := by
  simpa only [map_sum] using congrArg ψ (Coalgebra.sum_tmul_tmul_eq 𝓡 𝓡₁ 𝓡₂)

theorem sum_counit_smul' {a : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr B a ι𝓡) :
    ∑ i ∈ 𝓡.index, counit (R := B) (𝓡.right i) • 𝓡.left i = a := by
  simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using
    congrArg (TensorProduct.rid B H) (sum_tmul_counit_eq 𝓡)

def mulRepr {a b : H} {ι𝓡a : Type*} (𝓡a : Coalgebra.Repr B a ι𝓡a) {ι𝓡b : Type*} (𝓡b : Coalgebra.Repr B b ι𝓡b) :
    Coalgebra.Repr B (a * b) (ι𝓡a × ι𝓡b) where
  index := 𝓡a.index ×ˢ 𝓡b.index
  left := fun p => 𝓡a.left p.1 * 𝓡b.left p.2
  right := fun p => 𝓡a.right p.1 * 𝓡b.right p.2
  eq := by
    rw [Bialgebra.comul_mul, ← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum, Finset.sum_product]
    simp only [Algebra.TensorProduct.tmul_mul_tmul]

theorem collapse {a : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr B a ι𝓡) {κ : ι𝓡 → Type*}
    (𝓡₂ : ∀ m, Coalgebra.Repr B (𝓡.right m) (κ m)) :
    ∑ m ∈ 𝓡.index, ∑ i ∈ (𝓡₂ m).index,
        (𝓡.left m * antipode B ((𝓡₂ m).left i)) ⊗ₜ[B] (𝓡₂ m).right i = (1 : H) ⊗ₜ[B] a := by
  have h := sum_coassoc (TensorProduct.map (LinearMap.mul' B H ∘ₗ
      TensorProduct.map LinearMap.id (antipode B)) LinearMap.id ∘ₗ
    (TensorProduct.assoc B H H H).symm.toLinearMap) 𝓡 (fun m => ℛ B (𝓡.left m)) 𝓡₂
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, TensorProduct.assoc_symm_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mul'_apply] at h
  rw [← h]
  simp_rw [← TensorProduct.sum_tmul, sum_mul_antipode_eq_smul, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_sum, sum_counit_smul]

section Interface

variable (l : WithConv (H →ₗ[B] B)) (Λ : H)

theorem phi_apply (h x : H) :
    (toConv (l.ofConv ∘ₗ LinearMap.mulRight B h)) x = l.ofConv (x * h) := rfl

theorem phi_bijective [Module.Free B H] [Module.Finite B H]
    (hΨ : Function.Bijective
      (fun h : H => toConv (l.ofConv ∘ₗ LinearMap.mulRight B (antipode B h)))) :
    Function.Bijective (fun h : H => toConv (l.ofConv ∘ₗ LinearMap.mulRight B h)) := by
  classical

  let Φ : H →ₗ[B] Module.Dual B H :=
    LinearMap.mk₂ B (fun h x => l.ofConv (x * h))
      (fun h₁ h₂ x => by simp only [mul_add, map_add])
      (fun c h x => by simp only [mul_smul_comm, map_smul])
      (fun h x₁ x₂ => by simp only [add_mul, map_add])
      (fun c h x => by simp only [smul_mul_assoc, map_smul])
  have hΦ : ∀ h, Φ h = l.ofConv ∘ₗ LinearMap.mulRight B h := fun h => LinearMap.ext fun x => rfl
  have hsurj : Function.Surjective Φ := by
    intro f
    obtain ⟨h, hh⟩ := hΨ.2 (toConv f)
    exact ⟨antipode B h, by rw [hΦ]; exact toConv_injective hh⟩
  let b := Module.Free.chooseBasis B H
  let e : Module.Dual B H ≃ₗ[B] H := b.toDualEquiv.symm
  have hcomp : Function.Injective (e.toLinearMap ∘ₗ Φ) :=
    OrzechProperty.injective_of_surjective_endomorphism (e.toLinearMap ∘ₗ Φ)
      (e.surjective.comp hsurj)
  have hinj : Function.Injective Φ := fun x y hxy =>
    hcomp (by simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hxy])
  refine ⟨fun x y hxy => hinj ?_, fun f => ?_⟩
  · rw [hΦ, hΦ]
    exact toConv_injective hxy
  · obtain ⟨h, hh⟩ := hsurj f.ofConv
    refine ⟨h, ?_⟩
    change toConv (l.ofConv ∘ₗ LinearMap.mulRight B h) = f
    rw [← hΦ, hh, toConv_ofConv]

theorem eval_mul_integral
    (hΛ : toConv (l.ofConv ∘ₗ LinearMap.mulRight B Λ) = (1 : WithConv (H →ₗ[B] B))) (x : H) :
    l.ofConv (x * Λ) = counit (R := B) x := by
  have h := congrArg (fun g : WithConv (H →ₗ[B] B) => g x) hΛ
  simpa [LinearMap.convOne_apply] using h

theorem integral_pair_eval
    (hΛ : toConv (l.ofConv ∘ₗ LinearMap.mulRight B Λ) = (1 : WithConv (H →ₗ[B] B))) :
    l.ofConv Λ = 1 := by
  simpa [Bialgebra.counit_one] using eval_mul_integral l Λ hΛ 1

theorem leftIntegral_of_interface
    (hΦ : Function.Bijective (fun h : H => toConv (l.ofConv ∘ₗ LinearMap.mulRight B h)))
    (hΛ : toConv (l.ofConv ∘ₗ LinearMap.mulRight B Λ) = (1 : WithConv (H →ₗ[B] B))) (h : H) :
    h * Λ = counit (R := B) h • Λ := by
  apply hΦ.1
  refine WithConv.ext (LinearMap.ext fun x => ?_)
  change l.ofConv (x * (h * Λ)) = l.ofConv (x * (counit (R := B) h • Λ))
  rw [← mul_assoc, eval_mul_integral l Λ hΛ, Bialgebra.counit_mul, mul_smul_comm, map_smul,
    eval_mul_integral l Λ hΛ, smul_eq_mul, mul_comm]

theorem integral_left_smul [Module.Free B H]
    (hl : ∀ f : WithConv (H →ₗ[B] B), f * l = f 1 • l) {a : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr B a ι𝓡) :
    ∑ i ∈ 𝓡.index, l.ofConv (𝓡.right i) • 𝓡.left i = l.ofConv a • (1 : H) := by
  let b := Module.Free.chooseBasis B H
  refine b.ext_elem fun j => ?_
  have h := congrArg (fun g : WithConv (H →ₗ[B] B) => g a) (hl (toConv (b.coord j)))
  dsimp only at h
  rw [Coalgebra.Repr.convMul_apply 𝓡] at h
  simp only [WithConv.ofConv_smul, LinearMap.smul_apply, smul_eq_mul, b.coord_apply] at h
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  simpa only [mul_comm] using h

theorem sum_sum_eval_smul_antipode_mul [Module.Free B H]
    (hl : ∀ f : WithConv (H →ₗ[B] B), f * l = f 1 • l)
    (hΛ : toConv (l.ofConv ∘ₗ LinearMap.mulRight B Λ) = (1 : WithConv (H →ₗ[B] B)))
    {a : H} {ι𝓡a : Type*} (𝓡a : Coalgebra.Repr B a ι𝓡a) {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr B Λ ι𝓡) :
    ∑ i ∈ 𝓡a.index, ∑ k ∈ 𝓡.index, l.ofConv (𝓡a.right i * 𝓡.right k) •
        (antipode B (𝓡a.left i) * antipode B (𝓡.left k)) = counit (R := B) a • (1 : H) := by
  have h := integral_left_smul l hl (mulRepr 𝓡a 𝓡)
  simp only [mulRepr, Finset.sum_product] at h
  rw [eval_mul_integral l Λ hΛ] at h
  have h2 := congrArg (antipode B) h
  simpa only [map_sum, map_smul, antipode_mul, antipode_one, mul_comm] using h2

theorem casimir [Module.Free B H]
    (hl : ∀ f : WithConv (H →ₗ[B] B), f * l = f 1 • l)
    (hΛ : toConv (l.ofConv ∘ₗ LinearMap.mulRight B Λ) = (1 : WithConv (H →ₗ[B] B)))
    {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr B Λ ι𝓡) (y : H) :
    ∑ k ∈ 𝓡.index, l.ofConv (y * 𝓡.right k) • antipode B (𝓡.left k) = y := by

  let G : H →ₗ[B] H := ∑ k ∈ 𝓡.index,
    (l.ofConv ∘ₗ LinearMap.mulRight B (𝓡.right k)).smulRight (antipode B (𝓡.left k))
  have hG : ∀ w : H,
      G w = ∑ k ∈ 𝓡.index, l.ofConv (w * 𝓡.right k) • antipode B (𝓡.left k) := by
    intro w
    simp only [G, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
      LinearMap.mulRight_apply]

  have inner : ∀ w : H, ∑ i ∈ (ℛ B w).index,
      antipode B ((ℛ B w).left i) * G ((ℛ B w).right i) = counit (R := B) w • (1 : H) := by
    intro w
    simp_rw [hG, Finset.mul_sum, mul_smul_comm]
    exact sum_sum_eval_smul_antipode_mul l Λ hl hΛ (ℛ B w) 𝓡

  have key := congrArg (LinearMap.mul' B H ∘ₗ TensorProduct.map LinearMap.id G)
    (collapse (ℛ B y) fun m => ℛ B ((ℛ B y).right m))
  simp only [map_sum, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.mul'_apply, one_mul] at key
  rw [← hG y, ← key]
  simp_rw [mul_assoc, ← Finset.mul_sum, inner, mul_smul_comm, mul_one]
  exact sum_counit_smul' (ℛ B y)

theorem rank_eq [Module.Free B H] [Module.Finite B H]
    (hl : ∀ f : WithConv (H →ₗ[B] B), f * l = f 1 • l)
    (hΛ : toConv (l.ofConv ∘ₗ LinearMap.mulRight B Λ) = (1 : WithConv (H →ₗ[B] B))) :
    (Module.finrank B H : B) = counit (R := B) Λ * l.ofConv 1 := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Subsingleton.elim _ _
  let b := Module.Free.chooseBasis B H
  let 𝓡 := ℛ B Λ
  have hc : ∀ j, b.coord j
      (∑ k ∈ 𝓡.index, l.ofConv (b j * 𝓡.right k) • antipode B (𝓡.left k)) = 1 := by
    intro j
    rw [casimir l Λ hl hΛ 𝓡 (b j), b.coord_apply, b.repr_self, Finsupp.single_eq_same]
  have hexp : ∀ k ∈ 𝓡.index,
      ∑ j, b.coord j (antipode B (𝓡.left k)) * l.ofConv (b j * 𝓡.right k) =
        l.ofConv (antipode B (𝓡.left k) * 𝓡.right k) := by
    intro k _
    conv_rhs => rw [← b.sum_repr (antipode B (𝓡.left k))]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul, b.coord_apply]
  calc (Module.finrank B H : B) = (Fintype.card (Module.Free.ChooseBasisIndex B H) : B) := by
        rw [Module.finrank_eq_card_basis b]
    _ = ∑ j : Module.Free.ChooseBasisIndex B H, (1 : B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ = ∑ j, b.coord j
          (∑ k ∈ 𝓡.index, l.ofConv (b j * 𝓡.right k) • antipode B (𝓡.left k)) :=
        Finset.sum_congr rfl fun j _ => (hc j).symm
    _ = ∑ j, ∑ k ∈ 𝓡.index,
          b.coord j (antipode B (𝓡.left k)) * l.ofConv (b j * 𝓡.right k) := by
        simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = ∑ k ∈ 𝓡.index, l.ofConv (antipode B (𝓡.left k) * 𝓡.right k) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl hexp
    _ = l.ofConv (counit (R := B) Λ • (1 : H)) := by rw [← map_sum, sum_antipode_mul_eq_smul]
    _ = counit (R := B) Λ * l.ofConv 1 := by rw [map_smul, smul_eq_mul]

end Interface

end FinFlatHopf

namespace FinFlatHopf
p2m_export "FinFlatHopf" "exists_left_integral_frobenius"
p2m_open "FinFlatHopf"

open IsLocalRing

theorem eq_zero_or_one_of_idem {A : Type} [Ring A] [IsLocalRing A]
    (e : A) (he : e * e = e) : e = 0 ∨ e = 1 := by
  have hsum : e + (1 - e) = 1 := add_sub_cancel e 1
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with hu | hu
  ·
    right
    exact hu.mul_left_cancel (by rw [he, mul_one])
  ·
    left
    exact hu.mul_left_cancel (by rw [mul_zero, sub_mul, one_mul, he, sub_self])

variable {B : Type} [CommRing B] {H : Type} [CommRing H] [HopfAlgebra B H]

private lemma smul_convMul (r : B) (f g : WithConv (H →ₗ[B] B)) :
    (r • f) * g = r • (f * g) := by
  refine WithConv.ext (LinearMap.ext fun x => ?_)
  change ((r • f) * g).ofConv x = r • (f * g).ofConv x
  rw [(ℛ B x).convMul_apply, (ℛ B x).convMul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (r • f).ofConv _ * _ = r • (f.ofConv _ * _)
  rw [ofConv_smul, LinearMap.smul_apply, smul_mul_assoc]

private lemma convMul_smul (r : B) (f g : WithConv (H →ₗ[B] B)) :
    f * (r • g) = r • (f * g) := by
  refine WithConv.ext (LinearMap.ext fun x => ?_)
  change (f * (r • g)).ofConv x = r • (f * g).ofConv x
  rw [(ℛ B x).convMul_apply, (ℛ B x).convMul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ * (r • g).ofConv _ = r • (f.ofConv _ * _)
  rw [ofConv_smul, LinearMap.smul_apply, mul_smul_comm]

theorem counit_integral_mem [IsLocalRing B] [IsLocalRing H]
    [Module.Free B H] [Module.Finite B H] (hrank : 1 < Module.finrank B H)
    (l : WithConv (H →ₗ[B] B)) (Λ : H)
    (hΛint : ∀ h : H, h * Λ = counit (R := B) h • Λ)
    (hne : l.ofConv Λ = 1) :
    counit (R := B) Λ ∈ IsLocalRing.maximalIdeal B := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu

  set Λ' : H := (↑u⁻¹ : B) • Λ with hΛ'
  have hεΛ' : counit (R := B) Λ' = 1 := by
    simp only [hΛ', map_smul, smul_eq_mul, ← hu, Units.inv_mul]
  have hΛ'int : ∀ h : H, h * Λ' = counit (R := B) h • Λ' := fun h => by
    simp only [hΛ', mul_smul_comm, hΛint h, smul_smul, mul_comm]
  have hidem : Λ' * Λ' = Λ' := by
    rw [hΛ'int Λ', hεΛ', one_smul]
  rcases eq_zero_or_one_of_idem Λ' hidem with h0 | h1
  ·
    have hΛ0 : Λ = 0 := by
      have := h0
      rw [hΛ'] at this
      have := congrArg (fun x => (u : B) • x) this
      simpa [smul_smul, ← hu] using this
    exact one_ne_zero (by rw [← hne, hΛ0]; exact l.ofConv.map_zero)
  ·
    have hsurj : ∀ h : H, h = algebraMap B H (counit (R := B) h) := fun h => by
      have := hΛ'int h
      rw [h1, mul_one] at this
      rw [Algebra.algebraMap_eq_smul_one]; exact this

    have hinj : Function.Injective (Bialgebra.counitAlgHom B H).toLinearMap := fun h₁ h₂ heq =>
      (hsurj h₁).trans ((congrArg (algebraMap B H) heq).trans (hsurj h₂).symm)

    have hsurj' : Function.Surjective (Bialgebra.counitAlgHom B H).toLinearMap := fun b =>
      ⟨algebraMap B H b, (Bialgebra.counitAlgHom B H).commutes b⟩
    have heqv : H ≃ₗ[B] B :=
      LinearEquiv.ofBijective (Bialgebra.counitAlgHom B H).toLinearMap ⟨hinj, hsurj'⟩
    have : Module.finrank B H = 1 := by
      rw [heqv.finrank_eq, Module.finrank_self]
    omega

theorem eval_one_mem [IsLocalRing B]
    (l : WithConv (H →ₗ[B] B)) (Λ : H)
    (hl : ∀ f : WithConv (H →ₗ[B] B), f * l = (f.ofConv 1 : B) • l)
    (hH1 : IsLocalRing (WithConv (H →ₗ[B] B)))
    (hεΛ : counit (R := B) Λ ∈ IsLocalRing.maximalIdeal B)
    (hne : l.ofConv Λ = 1) :
    l.ofConv 1 ∈ IsLocalRing.maximalIdeal B := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu

  have hll : l * l = l.ofConv 1 • l := hl l

  set l' : WithConv (H →ₗ[B] B) := (↑u⁻¹ : B) • l with hl'
  have hll' : l * l = (↑u : B) • l := by rw [hu]; exact hll
  have hidem : l' * l' = l' := by
    rw [hl', smul_convMul, convMul_smul, hll', smul_smul, smul_smul,
        mul_assoc, u.inv_mul, mul_one]
  rcases @eq_zero_or_one_of_idem _ _ hH1 l' hidem with h0 | h1
  ·
    have hl0 : l = 0 := by
      have := congrArg (fun x => (u : B) • x) h0
      simpa [hl', smul_smul, ← hu] using this
    exact one_ne_zero (by rw [← hne, hl0]; rfl)
  ·
    have hleq : ∀ x : H, l.ofConv x = l.ofConv 1 * counit (R := B) x := fun x => by
      have h1x : (1 : WithConv (H →ₗ[B] B)).ofConv x = counit (R := B) x := by
        simp [LinearMap.convOne_apply (R := B) (A := B) (C := H) x]
      have hx : l'.ofConv x = (1 : WithConv (H →ₗ[B] B)).ofConv x :=
        congrArg (fun f => f.ofConv x) h1
      rw [h1x, hl', ofConv_smul, LinearMap.smul_apply, smul_eq_mul] at hx

      calc l.ofConv x
          = (↑u : B) * ((↑u⁻¹ : B) * l.ofConv x) := by rw [← mul_assoc, u.mul_inv, one_mul]
        _ = (↑u : B) * counit x := by rw [hx]
        _ = l.ofConv 1 * counit x := by rw [hu]
    have hone : l.ofConv 1 * counit (R := B) Λ = 1 := by rw [← hleq Λ, hne]
    have hεu : IsUnit (counit (R := B) Λ) :=
      isUnit_iff_exists.mpr ⟨l.ofConv 1, (mul_comm _ _).trans hone, hone⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp hεΛ hεu

section Assembly

variable (B : Type) [CommRing B] [IsLocalRing B]
variable (H : Type) [CommRing H] [HopfAlgebra B H] [Module.Free B H] [Module.Finite B H]

theorem not_isLocalRing_dual_of_isLocalRing_of_interface
    (n : ℕ) (hn1 : 1 < n) (hn : (n : B) ∉ IsLocalRing.maximalIdeal B ^ 2)
    (hrank : Module.finrank B H = n) [IsLocalRing H]
    (l : WithConv (H →ₗ[B] B))
    (hl : ∀ f : WithConv (H →ₗ[B] B), f * l = (f.ofConv 1 : B) • l)
    (hΦ : Function.Bijective
        (fun h : H => toConv (l.ofConv ∘ₗ LinearMap.mulRight B h)))
    (hIPE : ∀ Λ : H, toConv (l.ofConv ∘ₗ LinearMap.mulRight B Λ) = 1 → l.ofConv Λ = 1)
    (hLInt : ∀ Λ : H, toConv (l.ofConv ∘ₗ LinearMap.mulRight B Λ) = 1 →
        ∀ h : H, h * Λ = counit (R := B) h • Λ)
    (hRank : ∀ Λ : H, toConv (l.ofConv ∘ₗ LinearMap.mulRight B Λ) = 1 →
        (Module.finrank B H : B) = counit (R := B) Λ * l.ofConv 1) :
    ¬ IsLocalRing (WithConv (H →ₗ[B] B)) := by
  intro hdual

  obtain ⟨Λ, hΛ⟩ := hΦ.2 1

  have hεΛ : counit (R := B) Λ ∈ IsLocalRing.maximalIdeal B :=
    counit_integral_mem (hrank ▸ hn1) l Λ (hLInt Λ hΛ) (hIPE Λ hΛ)
  have hl1 : l.ofConv 1 ∈ IsLocalRing.maximalIdeal B :=
    eval_one_mem l Λ hl hdual hεΛ (hIPE Λ hΛ)

  have : (n : B) ∈ IsLocalRing.maximalIdeal B ^ 2 := by
    rw [← hrank, hRank Λ hΛ, sq]
    exact Ideal.mul_mem_mul hεΛ hl1
  exact hn this

end Assembly

end FinFlatHopf

theorem solution
    (B : Type) [CommRing B] [IsLocalRing B] (n : ℕ) (hn1 : 1 < n)
    (hn : (n : B) ∉ IsLocalRing.maximalIdeal B ^ 2)
    (H : Type) [CommRing H] [HopfAlgebra B H] [Module.Free B H] [Module.Finite B H]
    (hrank : Module.finrank B H = n) [IsLocalRing H] :
    ¬ IsLocalRing (WithConv (H →ₗ[B] B)) := by
  obtain ⟨l, hl, hΨ⟩ := FinFlatHopf.exists_left_integral_frobenius B H
  have hΦ := FinFlatHopf.phi_bijective l hΨ
  exact FinFlatHopf.not_isLocalRing_dual_of_isLocalRing_of_interface B H n hn1 hn hrank l hl hΦ
    (fun Λ hΛ => FinFlatHopf.integral_pair_eval l Λ hΛ)
    (fun Λ hΛ => FinFlatHopf.leftIntegral_of_interface l Λ hΦ hΛ)
    (fun Λ hΛ => FinFlatHopf.rank_eq l Λ hl hΛ)

end

end S_FinFlatHopf_not_isLocalRing_dual_of_isLocalRing
end P2MW
export P2MW.S_FinFlatHopf_not_isLocalRing_dual_of_isLocalRing (solution)
