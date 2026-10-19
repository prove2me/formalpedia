-- Prove2me | solution 1 for GNFS.congruence_of_squares
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:19:49.733989+00:00
-- url     : https://prove2.me/submissions/26870c8c-d8f0-43b8-a16e-ba1b20b67d17

import Mathlib
import Definitions.Def_GNFS_defs
open Polynomial

namespace GNFSHom

/-- If `f` is irreducible in `ℤ[X]` and `θ` is a root, every integer polynomial vanishing at
`θ` is a multiple of `f` (Gauss's lemma). -/
lemma dvd_of_aeval_eq_zero (f : ℤ[X]) (hf : Irreducible f) (θ : ℂ) (hθ : aeval θ f = 0)
    (p : ℤ[X]) (hp : aeval θ p = 0) : f ∣ p := by
  have hdeg : f.natDegree ≠ 0 := by
    intro h
    rw [eq_C_of_natDegree_eq_zero h, aeval_C] at hθ
    rw [eq_intCast, Int.cast_eq_zero] at hθ
    have : f.coeff 0 = 0 := hθ
    apply hf.ne_zero
    rw [eq_C_of_natDegree_eq_zero h, this, C_0]
  have hprim : f.IsPrimitive := hf.isPrimitive hdeg
  rw [hprim.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ)]
  have hirr : Irreducible (f.map (algebraMap ℤ ℚ)) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hf
  have hθ' : aeval θ (f.map (algebraMap ℤ ℚ)) = 0 := by rw [aeval_map_algebraMap]; exact hθ
  have hp' : aeval θ (p.map (algebraMap ℤ ℚ)) = 0 := by rw [aeval_map_algebraMap]; exact hp
  have hmin := minpoly.eq_of_irreducible hirr hθ'
  have hdvd : minpoly ℚ θ ∣ p.map (algebraMap ℤ ℚ) := minpoly.dvd ℚ θ hp'
  rw [← hmin] at hdvd
  exact (dvd_mul_right _ _).trans hdvd

end GNFSHom

open GNFSHom in
theorem exists_hom (f : ℤ[X]) (hf : Irreducible f) (θ : ℂ)
    (hθ : aeval θ f = 0) (n : ℕ) (m : ℤ) (hm : (n : ℤ) ∣ f.eval m) :
    ∃ φ : Algebra.adjoin ℤ ({θ} : Set ℂ) →+* ZMod n,
      φ ⟨θ, Algebra.self_mem_adjoin_singleton ℤ θ⟩ = (m : ZMod n) := by
  set A := Algebra.adjoin ℤ ({θ} : Set ℂ)
  set t : A := ⟨θ, Algebra.self_mem_adjoin_singleton ℤ θ⟩
  let ψ : ℤ[X] →+* A := (aeval t).toRingHom
  have hψ : ∀ p : ℤ[X], ((ψ p : A) : ℂ) = aeval θ p := by
    intro p
    show ((aeval t p : A) : ℂ) = aeval θ p
    rw [← Subalgebra.aeval_coe]
  have hsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Algebra.adjoin ℤ ({θ} : Set ℂ) := hy
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    exact ⟨p, Subtype.ext (hψ p)⟩
  let χ : ℤ[X] →+* ZMod n := eval₂RingHom (Int.castRingHom (ZMod n)) (m : ZMod n)
  have hker : RingHom.ker ψ ≤ RingHom.ker χ := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    have h0 : aeval θ p = 0 := by rw [← hψ p, hp]; rfl
    obtain ⟨q, rfl⟩ := dvd_of_aeval_eq_zero f hf θ hθ p h0
    rw [map_mul]
    have : χ f = 0 := by
      show eval₂ (Int.castRingHom (ZMod n)) (Int.castRingHom (ZMod n) m) f = 0
      rw [eval₂_hom, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hm
    rw [this, zero_mul]
  refine ⟨(ψ.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj))
    ⟨χ, hker⟩, ?_⟩
  have : ψ X = t := by simp [ψ]
  rw [← this, RingHom.liftOfRightInverse_comp_apply]
  simp [χ]

namespace GNFSGoal

lemma image_sq (θ : ℂ) (n : ℕ) (m : ℤ) (S : Finset (ℤ × ℤ))
    (γ : Algebra.adjoin ℤ ({θ} : Set ℂ))
    (hγ : (γ : ℂ) ^ 2 = ∏ p ∈ S, ((p.1 : ℂ) - (p.2 : ℂ) * θ))
    (φ : Algebra.adjoin ℤ ({θ} : Set ℂ) →+* ZMod n)
    (hφ : φ ⟨θ, Algebra.self_mem_adjoin_singleton ℤ θ⟩ = (m : ZMod n)) :
    φ γ ^ 2 = ∏ p ∈ S, ((p.1 : ZMod n) - (p.2 : ZMod n) * (m : ZMod n)) := by
  set t : Algebra.adjoin ℤ ({θ} : Set ℂ) := ⟨θ, Algebra.self_mem_adjoin_singleton ℤ θ⟩
  have h : γ ^ 2 = ∏ p ∈ S, (((p.1 : ℤ) : Algebra.adjoin ℤ ({θ} : Set ℂ)) -
      ((p.2 : ℤ) : Algebra.adjoin ℤ ({θ} : Set ℂ)) * t) := by
    apply Subtype.ext
    push_cast
    rw [hγ]
  rw [← map_pow, h, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, map_mul, map_intCast, map_intCast, hφ]

end GNFSGoal

open GNFSGoal in
theorem solution (n : ℕ) (m : ℤ) (f₁ f₂ : ℤ[X])
    (hf₁ : Irreducible f₁) (hf₂ : Irreducible f₂) (θ₁ θ₂ : ℂ)
    (hθ₁ : aeval θ₁ f₁ = 0) (hθ₂ : aeval θ₂ f₂ = 0)
    (hm₁ : (n : ℤ) ∣ f₁.eval m) (hm₂ : (n : ℤ) ∣ f₂.eval m)
    (S : Finset (ℤ × ℤ))
    (γ₁ : Algebra.adjoin ℤ ({θ₁} : Set ℂ)) (γ₂ : Algebra.adjoin ℤ ({θ₂} : Set ℂ))
    (hγ₁ : (γ₁ : ℂ) ^ 2 = ∏ p ∈ S, ((p.1 : ℂ) - (p.2 : ℂ) * θ₁))
    (hγ₂ : (γ₂ : ℂ) ^ 2 = ∏ p ∈ S, ((p.1 : ℂ) - (p.2 : ℂ) * θ₂)) :
    (∃ φ₁ : Algebra.adjoin ℤ ({θ₁} : Set ℂ) →+* ZMod n,
        φ₁ ⟨θ₁, Algebra.self_mem_adjoin_singleton ℤ θ₁⟩ = (m : ZMod n)) ∧
      (∃ φ₂ : Algebra.adjoin ℤ ({θ₂} : Set ℂ) →+* ZMod n,
        φ₂ ⟨θ₂, Algebra.self_mem_adjoin_singleton ℤ θ₂⟩ = (m : ZMod n)) ∧
      ∀ (φ₁ : Algebra.adjoin ℤ ({θ₁} : Set ℂ) →+* ZMod n)
        (φ₂ : Algebra.adjoin ℤ ({θ₂} : Set ℂ) →+* ZMod n),
        φ₁ ⟨θ₁, Algebra.self_mem_adjoin_singleton ℤ θ₁⟩ = (m : ZMod n) →
        φ₂ ⟨θ₂, Algebra.self_mem_adjoin_singleton ℤ θ₂⟩ = (m : ZMod n) →
        φ₁ γ₁ ^ 2 = φ₂ γ₂ ^ 2 := by
  refine ⟨exists_hom f₁ hf₁ θ₁ hθ₁ n m hm₁, exists_hom f₂ hf₂ θ₂ hθ₂ n m hm₂, ?_⟩
  intro φ₁ φ₂ h₁ h₂
  rw [image_sq θ₁ n m S γ₁ hγ₁ φ₁ h₁, image_sq θ₂ n m S γ₂ hγ₂ φ₂ h₂]
