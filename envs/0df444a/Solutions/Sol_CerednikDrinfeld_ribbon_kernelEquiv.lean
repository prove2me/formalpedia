-- Prove2me | solution 1 for CerednikDrinfeld.ribbon_kernelEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/97563c98-081b-50b3-8f50-b43cb94df6e7

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CerednikDrinfeld_Ribbon
import Definitions.Def_ModularCurve_ComponentGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Finiteness.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_ribbon_kernelEquiv

set_option Elab.async false

set_option autoImplicit false

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "DegeneracyData degeneracyMatrix pushforward jointDelta ribbonKernel mem_ribbonKernel ribbonGram ribbonGram_apply ribbonComponentGroup HeckeData heckeKernelMap Matching"
p2m_open "CerednikDrinfeld"

open ModularCurve

variable {E₁ V₁ E₂ V₂ : Type*}

section Proofs

variable [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂]
  [DecidableEq V₂] {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂}

omit [Fintype V₁] [Fintype V₂] in

private theorem pushforward_comp_symm (eE : E₁ ≃ E₂) (eV : V₁ ≃ V₂) {f₁ : E₁ → V₁} {f₂ : E₂ → V₂}
    (hf : ∀ e, f₂ (eE e) = eV (f₁ e)) (x : E₁ → ℤ) :
    pushforward f₂ (x ∘ eE.symm) = (pushforward f₁ x) ∘ eV.symm := by
  funext v
  simp only [pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    degeneracyMatrix, Matrix.of_apply, Function.comp_apply]
  rw [← Equiv.sum_comp eE fun e₂ => (if f₂ e₂ = v then (1 : ℤ) else 0) * x (eE.symm e₂)]
  refine Finset.sum_congr rfl fun e₁ _ => ?_
  simp only [Equiv.symm_apply_apply, hf]
  congr 1
  simp [Equiv.apply_eq_iff_eq_symm_apply]

omit [Fintype V₁] [Fintype V₂] in
private theorem comp_symm_mem_ribbonKernel {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂}
    (eE : E₁ ≃ E₂) (eV : V₁ ≃ V₂)
    (ha : ∀ e, D₂.a (eE e) = eV (D₁.a e)) (hb : ∀ e, D₂.b (eE e) = eV (D₁.b e))
    {x : E₁ → ℤ} (hx : x ∈ ribbonKernel D₁) :
    (x ∘ eE.symm) ∈ ribbonKernel D₂ := by
  rw [mem_ribbonKernel] at hx ⊢
  have hpa : pushforward D₂.a (x ∘ eE.symm) = 0 := by
    have h0 : pushforward D₁.a x = 0 := by simpa [jointDelta] using hx 0
    rw [pushforward_comp_symm eE eV ha x, h0]
    funext v
    simp
  have hpb : pushforward D₂.b (x ∘ eE.symm) = 0 := by
    have h0 : pushforward D₁.b x = 0 := by simpa [jointDelta] using hx 1
    rw [pushforward_comp_symm eE eV hb x, h0]
    funext v
    simp
  intro i
  fin_cases i
  · simpa [jointDelta] using hpa
  · simpa [jointDelta] using hpb

private theorem comp_mem_ribbonKernel {H₁ : HeckeData D₁} {H₂ : HeckeData D₂}
    (M : Matching H₁ H₂) {y : E₂ → ℤ} (hy : y ∈ ribbonKernel D₂) :
    (y ∘ M.eE) ∈ ribbonKernel D₁ := by
  have hfa : ∀ e₂, D₁.a (M.eE.symm e₂) = M.eV.symm (D₂.a e₂) := by
    intro e₂
    have h := M.map_a (M.eE.symm e₂)
    simp only [Equiv.apply_symm_apply] at h
    rw [h, Equiv.symm_apply_apply]
  have hfb : ∀ e₂, D₁.b (M.eE.symm e₂) = M.eV.symm (D₂.b e₂) := by
    intro e₂
    have h := M.map_b (M.eE.symm e₂)
    simp only [Equiv.apply_symm_apply] at h
    rw [h, Equiv.symm_apply_apply]
  have key := comp_symm_mem_ribbonKernel M.eE.symm M.eV.symm hfa hfb hy
  simpa [Equiv.symm_symm] using key

private theorem ribbon_kernelEquiv (H₁ : HeckeData D₁) (H₂ : HeckeData D₂)
    (M : Matching H₁ H₂) :
    ∃ e : ribbonKernel D₁ ≃ₗ[ℤ] ribbonKernel D₂,
      (∀ (ℓ : Nat.Primes) (x : ribbonKernel D₁),
        e (heckeKernelMap H₁ ℓ x) = heckeKernelMap H₂ ℓ (e x)) ∧
      (∀ x y : ribbonKernel D₁, ribbonGram D₂ (e x) (e y) = ribbonGram D₁ x y) := by
  classical
  let R : (E₁ → ℤ) ≃ₗ[ℤ] (E₂ → ℤ) := LinearEquiv.piCongrLeft' ℤ (fun _ => ℤ) M.eE
  have hRval : ∀ x : E₁ → ℤ, R x = x ∘ M.eE.symm := fun _ => rfl
  have hmap : (ribbonKernel D₁).map (R : (E₁ → ℤ) →ₗ[ℤ] (E₂ → ℤ)) = ribbonKernel D₂ := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact comp_symm_mem_ribbonKernel M.eE M.eV M.map_a M.map_b hx
    · intro y hy
      refine ⟨y ∘ M.eE, comp_mem_ribbonKernel M hy, ?_⟩
      funext i
      simp [hRval, Function.comp_apply]
  refine ⟨(R.submoduleMap (ribbonKernel D₁)).trans (LinearEquiv.ofEq _ _ hmap), ?_, ?_⟩
  · intro ℓ x
    apply Subtype.ext
    have hv₁ : (((R.submoduleMap (ribbonKernel D₁)).trans
        (LinearEquiv.ofEq _ _ hmap)) (heckeKernelMap H₁ ℓ x) : E₂ → ℤ)
        = ((H₁.T ℓ).mulVecLin x.1) ∘ M.eE.symm := rfl
    have hv₂ : ((heckeKernelMap H₂ ℓ (((R.submoduleMap (ribbonKernel D₁)).trans
        (LinearEquiv.ofEq _ _ hmap)) x)) : E₂ → ℤ)
        = (H₂.T ℓ).mulVecLin (x.1 ∘ M.eE.symm) := rfl
    rw [hv₁, hv₂]
    by_cases hℓ : ℓ ∈ M.bad
    · exact (M.bad_kernel_intertwine ℓ hℓ x.1 x.2).symm
    · exact (M.away_intertwine ℓ hℓ x.1).symm
  · intro x y
    have hvx : (((R.submoduleMap (ribbonKernel D₁)).trans
        (LinearEquiv.ofEq _ _ hmap)) x : E₂ → ℤ) = x.1 ∘ M.eE.symm := rfl
    have hvy : (((R.submoduleMap (ribbonKernel D₁)).trans
        (LinearEquiv.ofEq _ _ hmap)) y : E₂ → ℤ) = y.1 ∘ M.eE.symm := rfl
    simp only [ribbonGram_apply, hvx, hvy, Function.comp_apply]
    rw [← Equiv.sum_comp M.eE
      (fun e₂ => ((D₂.w e₂ : ℕ) : ℤ) * (x.1 (M.eE.symm e₂) * y.1 (M.eE.symm e₂)))]
    refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [M.map_w, Equiv.symm_apply_apply]

private theorem ribbon_linearEquiv_of_anchors (H₁ : HeckeData D₁) (H₂ : HeckeData D₂)
    (M : Matching H₁ H₂) {Ymod Zmod : Type*}
    [AddCommGroup Ymod] [Module HeckeAlg Ymod] [AddCommGroup Zmod] [Module HeckeAlg Zmod]
    (eY : Ymod ≃+ ribbonKernel D₁)
    (hY : ∀ (ℓ : Nat.Primes) (m : Ymod),
      eY (heckeGen ℓ • m) = heckeKernelMap H₁ ℓ (eY m))
    (eZ : Zmod ≃+ ribbonKernel D₂)
    (hZ : ∀ (ℓ : Nat.Primes) (m : Zmod),
      eZ (heckeGen ℓ • m) = heckeKernelMap H₂ ℓ (eZ m)) :
    Nonempty (Ymod ≃ₗ[HeckeAlg] Zmod) := by
  obtain ⟨e, he, -⟩ := ribbon_kernelEquiv H₁ H₂ M
  let φ₀ : Ymod ≃+ Zmod := (eY.trans e.toAddEquiv).trans eZ.symm
  have hφ₀ : ∀ m, φ₀ m = eZ.symm (e (eY m)) := fun _ => rfl
  have hZ' : ∀ (ℓ : Nat.Primes) (k : ribbonKernel D₂),
      eZ.symm (heckeKernelMap H₂ ℓ k) = heckeGen ℓ • eZ.symm k := by
    intro ℓ k
    apply eZ.injective
    rw [hZ ℓ (eZ.symm k), AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hgen : ∀ (ℓ : Nat.Primes) (m : Ymod),
      φ₀ (heckeGen ℓ • m) = heckeGen ℓ • φ₀ m := by
    intro ℓ m
    rw [hφ₀, hφ₀, hY, he, hZ']
  have hgenX : ∀ (ℓ : Nat.Primes) (m : Ymod),
      φ₀ ((MvPolynomial.X ℓ : HeckeAlg) • m) = (MvPolynomial.X ℓ : HeckeAlg) • φ₀ m := hgen
  have hsmul : ∀ (r : HeckeAlg) (m : Ymod), φ₀ (r • m) = r • φ₀ m := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a =>
        intro m
        have hCa : (MvPolynomial.C a : HeckeAlg) = ((a : ℤ) : HeckeAlg) :=
          eq_intCast (MvPolynomial.C (σ := Nat.Primes) (R := ℤ)) a
        rw [hCa, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]
    | add p q hp hq =>
        intro m
        rw [add_smul, map_add, hp m, hq m, add_smul]
    | mul_X p ℓ hp =>
        intro m
        rw [mul_smul, mul_smul, hp, hgenX]
  exact ⟨AddEquiv.toLinearEquiv φ₀ hsmul⟩

private theorem ribbon_annihilator_eq_of_anchors (H₁ : HeckeData D₁) (H₂ : HeckeData D₂)
    (M : Matching H₁ H₂) {Ymod Zmod : Type*}
    [AddCommGroup Ymod] [Module HeckeAlg Ymod] [AddCommGroup Zmod] [Module HeckeAlg Zmod]
    (eY : Ymod ≃+ ribbonKernel D₁)
    (hY : ∀ (ℓ : Nat.Primes) (m : Ymod),
      eY (heckeGen ℓ • m) = heckeKernelMap H₁ ℓ (eY m))
    (eZ : Zmod ≃+ ribbonKernel D₂)
    (hZ : ∀ (ℓ : Nat.Primes) (m : Zmod),
      eZ (heckeGen ℓ • m) = heckeKernelMap H₂ ℓ (eZ m)) :
    Module.annihilator HeckeAlg Ymod = Module.annihilator HeckeAlg Zmod := by
  obtain ⟨φ⟩ := ribbon_linearEquiv_of_anchors H₁ H₂ M eY hY eZ hZ
  exact φ.annihilator_eq

private theorem ribbon_quotient_equiv_of_anchors (H₁ : HeckeData D₁) (H₂ : HeckeData D₂)
    (M : Matching H₁ H₂) {Ymod Zmod : Type*}
    [AddCommGroup Ymod] [Module HeckeAlg Ymod] [AddCommGroup Zmod] [Module HeckeAlg Zmod]
    (eY : Ymod ≃+ ribbonKernel D₁)
    (hY : ∀ (ℓ : Nat.Primes) (m : Ymod),
      eY (heckeGen ℓ • m) = heckeKernelMap H₁ ℓ (eY m))
    (eZ : Zmod ≃+ ribbonKernel D₂)
    (hZ : ∀ (ℓ : Nat.Primes) (m : Zmod),
      eZ (heckeGen ℓ • m) = heckeKernelMap H₂ ℓ (eZ m))
    (𝔪 : Ideal HeckeAlg) :
    Nonempty ((Ymod ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Ymod)))
      ≃ₗ[HeckeAlg] (Zmod ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Zmod)))) := by
  obtain ⟨φ⟩ := ribbon_linearEquiv_of_anchors H₁ H₂ M eY hY eZ hZ
  refine ⟨Submodule.Quotient.equiv _ _ φ ?_⟩
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

private theorem ribbon_componentGroup_equiv_of_isometry
    (e : ribbonKernel D₁ ≃ₗ[ℤ] ribbonKernel D₂)
    (hiso : ∀ x y : ribbonKernel D₁, ribbonGram D₂ (e x) (e y) = ribbonGram D₁ x y) :
    Nonempty (ribbonComponentGroup D₁ ≃ₗ[ℤ] ribbonComponentGroup D₂) := by
  have key : (e.symm.dualMap : Module.Dual ℤ (ribbonKernel D₁) →ₗ[ℤ]
      Module.Dual ℤ (ribbonKernel D₂)).comp (ribbonGram D₁) = (ribbonGram D₂).comp e.toLinearMap := by
    ext x z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.dualMap_apply]
    rw [← hiso x (e.symm z), LinearEquiv.apply_symm_apply]
  refine ⟨Submodule.Quotient.equiv _ _ e.symm.dualMap ?_⟩
  rw [← LinearMap.range_comp, key, LinearMap.range_comp_of_range_eq_top _ e.range]

private theorem ribbon_componentGroup_equiv (H₁ : HeckeData D₁) (H₂ : HeckeData D₂)
    (M : Matching H₁ H₂) :
    Nonempty (ribbonComponentGroup D₁ ≃ₗ[ℤ] ribbonComponentGroup D₂) := by
  obtain ⟨e, -, hiso⟩ := ribbon_kernelEquiv H₁ H₂ M
  exact ribbon_componentGroup_equiv_of_isometry e hiso

end Proofs

set_option pp.funBinderTypes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 20000
#check @CerednikDrinfeld.ribbon_kernelEquiv
#check @CerednikDrinfeld.ribbon_componentGroup_equiv

end CerednikDrinfeld

set_option autoImplicit false
open ModularCurve
universe u_1 u_2 u_3 u_4
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_ribbon_kernelEquiv.CerednikDrinfeld"

theorem solution :
    ∀ {E₁ : Type u_1} {V₁ : Type u_2} {E₂ : Type u_3} {V₂ : Type u_4}
  [inst : Fintype E₁] [inst_1 : Fintype V₁] [inst_2 : DecidableEq V₁] [inst_3 : Fintype E₂] [inst_4 : Fintype V₂]
  [inst_5 : DecidableEq V₂] {D₁ : CerednikDrinfeld.DegeneracyData E₁ V₁} {D₂ : CerednikDrinfeld.DegeneracyData E₂ V₂}
  (H₁ : CerednikDrinfeld.HeckeData D₁) (H₂ : CerednikDrinfeld.HeckeData D₂) (M : CerednikDrinfeld.Matching H₁ H₂),
  ∃ (e : ↥(CerednikDrinfeld.ribbonKernel D₁) ≃ₗ[ℤ] ↥(CerednikDrinfeld.ribbonKernel D₂)),
    (∀ (ℓ : Nat.Primes) (x : ↥(CerednikDrinfeld.ribbonKernel D₁)),
        e ((CerednikDrinfeld.heckeKernelMap H₁ ℓ) x) = (CerednikDrinfeld.heckeKernelMap H₂ ℓ) (e x)) ∧
      ∀ (x y : ↥(CerednikDrinfeld.ribbonKernel D₁)),
        ((CerednikDrinfeld.ribbonGram D₂) (e x)) (e y) = ((CerednikDrinfeld.ribbonGram D₁) x) y := @CerednikDrinfeld.ribbon_kernelEquiv

end S_CerednikDrinfeld_ribbon_kernelEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_ribbon_kernelEquiv (solution)
