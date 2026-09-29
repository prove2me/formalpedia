-- Prove2me | solution 1 for CerednikDrinfeld.exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b1fcc8dd-ee07-577d-a0c2-7d310a3f2375

import Definitions.Def_CerednikDrinfeld_Ribbon
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv

set_option autoImplicit false

open CerednikDrinfeld

namespace RX

section Helpers

variable {E V : Type} [Fintype E] [DecidableEq V]

private theorem pushforward_apply (f : E → V) (x : E → ℤ) (v : V) :
    pushforward f x v = ∑ e, if f e = v then x e else 0 := by
  simp only [pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply, ite_mul,
    one_mul, zero_mul]

private theorem mem_ribbonKernel_iff' (D : DegeneracyData E V) (x : E → ℤ) :
    x ∈ ribbonKernel D ↔ pushforward D.a x = 0 ∧ pushforward D.b x = 0 := by
  rw [mem_ribbonKernel, Fin.forall_fin_two]
  simp [jointDelta]

end Helpers

end RX

open RX in

theorem solution
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [DecidableEq V₁] [Fintype E₂] [DecidableEq V₂]
    (D₁ : DegeneracyData E₁ V₁) (D₂ : DegeneracyData E₂ V₂)
    (eE : E₁ ≃ E₂) (eV : V₁ ≃ V₂)
    (ha : ∀ e, D₂.a (eE e) = eV (D₁.a e)) (hb : ∀ e, D₂.b (eE e) = eV (D₁.b e)) (hw : ∀ e, D₂.w (eE e) = D₁.w e) :
    ∃ φ : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂),
      (∀ (x : ↥(ribbonKernel D₁)) (e : E₁), (φ x : E₂ → ℤ) (eE e) = (x : E₁ → ℤ) e) ∧
      (∀ x y : ↥(ribbonKernel D₁), ribbonGram D₂ (φ x) (φ y) = ribbonGram D₁ x y) := by
  classical

  let φ₀ : (E₁ → ℤ) ≃ₗ[ℤ] (E₂ → ℤ) := LinearEquiv.funCongrLeft ℤ ℤ eE.symm
  have hφ₀ : ∀ (x : E₁ → ℤ) (e₂ : E₂), φ₀ x e₂ = x (eE.symm e₂) := fun x e₂ => rfl

  have key : ∀ (f₁ : E₁ → V₁) (f₂ : E₂ → V₂), (∀ e, f₂ (eE e) = eV (f₁ e)) →
      ∀ (x : E₁ → ℤ) (v₂ : V₂), pushforward f₂ (φ₀ x) v₂ = pushforward f₁ x (eV.symm v₂) := by
    intro f₁ f₂ hf x v₂
    rw [pushforward_apply, pushforward_apply, ← Equiv.sum_comp eE]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hφ₀, Equiv.symm_apply_apply, hf]
    have hiff : eV (f₁ e) = v₂ ↔ f₁ e = eV.symm v₂ := Equiv.apply_eq_iff_eq_symm_apply eV
    by_cases hc : f₁ e = eV.symm v₂
    · rw [if_pos (hiff.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
  have hmem : ∀ x : E₁ → ℤ, x ∈ ribbonKernel D₁ ↔ φ₀ x ∈ ribbonKernel D₂ := by
    intro x
    rw [mem_ribbonKernel_iff', mem_ribbonKernel_iff']
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨funext fun v₂ => ?_, funext fun v₂ => ?_⟩
      · rw [key D₁.a D₂.a ha, h1]; rfl
      · rw [key D₁.b D₂.b hb, h2]; rfl
    · rintro ⟨h1, h2⟩
      refine ⟨funext fun v₁ => ?_, funext fun v₁ => ?_⟩
      · have := congrFun h1 (eV v₁); rw [key D₁.a D₂.a ha, Equiv.symm_apply_apply] at this; exact this
      · have := congrFun h2 (eV v₁); rw [key D₁.b D₂.b hb, Equiv.symm_apply_apply] at this; exact this
  have hmap : (ribbonKernel D₁).map (φ₀ : (E₁ → ℤ) →ₗ[ℤ] (E₂ → ℤ)) = ribbonKernel D₂ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmem x).mp hx
    · intro y hy
      refine ⟨φ₀.symm y, ?_, by simp⟩
      show φ₀.symm y ∈ ribbonKernel D₁
      rw [hmem, LinearEquiv.apply_symm_apply]
      exact hy
  refine ⟨LinearEquiv.ofSubmodules φ₀ _ _ hmap, fun x e => ?_, fun x y => ?_⟩
  · show φ₀ (x : E₁ → ℤ) (eE e) = (x : E₁ → ℤ) e
    rw [hφ₀, Equiv.symm_apply_apply]
  · rw [ribbonGram_apply, ribbonGram_apply, ← Equiv.sum_comp eE]
    refine Finset.sum_congr rfl fun e _ => ?_
    show (D₂.w (eE e) : ℤ) * (φ₀ (x : E₁ → ℤ) (eE e) * φ₀ (y : E₁ → ℤ) (eE e)) = _
    rw [hw, hφ₀, hφ₀, Equiv.symm_apply_apply]

end S_CerednikDrinfeld_exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv
end P2MW
export P2MW.S_CerednikDrinfeld_exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv (solution)
