-- Prove2me | solution 1 for GNFS.exists_ringHom_adjoin_zmod
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:53:05.976564+00:00
-- url     : https://prove2.me/submissions/fc8768a3-910c-4e95-ba37-1a62ab9b19dd

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
theorem solution (f : ℤ[X]) (hf : Irreducible f) (θ : ℂ)
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
