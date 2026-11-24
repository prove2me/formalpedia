-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_lift_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:23.66702+00:00
-- url     : https://prove2.me/submissions/c44965b0-d310-4bb4-b2d2-5b77f337d401

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_uniform
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_preimage
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_entSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_hermSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_quad_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
namespace Formalism.HermitianLattices.Ext.L3.HermitianSublattices
theorem _root_.solution [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a)) (𝔟 : Ideal A) (h𝔟s : ∀ a ∈ 𝔟, star a ∈ 𝔟)
    (h𝔟2 : ∀ a ∈ 𝔟, ∀ b ∈ 𝔟, a * b = 0) (H : Matrix m m A) (hH : Hᴴ = H) (T : Matrix r r A)
    (hT : Tᴴ = T) (p' : Matrix m r A' → Prop)
    (hinv : ∀ X Y : Matrix m r A, Y ∈ entSub m r 𝔟 → (p' ((X + Y).map π) ↔ p' (X.map π)))
    (RC : ∀ X : Matrix m r A, p' (X.map π) → (∀ i j, (Xᴴ * H * X - T) i j ∈ RingHom.ker π) →
      ∀ S ∈ hermSub r (RingHom.ker π), ∃ Y ∈ entSub m r 𝔟, Xᴴ * H * Y + Yᴴ * H * X = S) :
    Nat.card {X : Matrix m r A // p' (X.map π) ∧ Xᴴ * H * X = T} *
        Nat.card (hermSub r (RingHom.ker π)) =
      Nat.card (entSub m r (RingHom.ker π)) *
        Nat.card {X' : Matrix m r A' // p' X' ∧ X'ᴴ * (H.map π) * X' = T.map π} := by
  classical
  haveI : Finite (Matrix m r A) := inferInstanceAs (Finite (m → r → A))
  let f : Matrix m r A →+ Matrix m r A' :=
    { toFun := fun X => X.map π
      map_zero' := by ext i j; simp
      map_add' := fun X Y => by ext i j; simp }
  have hfs : Function.Surjective f := fun X' =>
    ⟨X'.map (Function.surjInv hπ), by
      ext i j
      show π (Function.surjInv hπ (X' i j)) = X' i j
      exact Function.surjInv_eq hπ (X' i j)⟩
  have hkerf : f.ker = entSub m r (RingHom.ker π) := by
    ext X
    rw [AddMonoidHom.mem_ker, mem_entSub]
    constructor
    · intro h i j
      have h' := congrFun (congrFun h i) j
      rw [RingHom.mem_ker]
      exact h'
    · intro h
      ext i j
      exact RingHom.mem_ker.mp (h i j)
  have hmap : ∀ X : Matrix m r A, (Xᴴ * H * X).map π = (X.map π)ᴴ * H.map π * X.map π := by
    intro X
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map (⇑π) hπs]
  have hiff : ∀ X : Matrix m r A,
      (p' (X.map π) ∧ Xᴴ * H * X - T ∈ hermSub r (RingHom.ker π)) ↔
        (p' (f X) ∧ (f X)ᴴ * H.map π * f X = T.map π) := by
    intro X
    rw [mem_hermSub]
    have hh : (Xᴴ * H * X - T)ᴴ = Xᴴ * H * X - T := by
      rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH,
        hT, Matrix.mul_assoc]
    have hf : f X = X.map π := rfl
    rw [hf, ← hmap]
    constructor
    · rintro ⟨hp, -, hk⟩
      refine ⟨hp, ?_⟩
      ext i j
      have h' := hk i j
      rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero] at h'
      simp only [Matrix.map_apply]
      exact h'
    · rintro ⟨hp, he'⟩
      refine ⟨hp, hh, fun i j => ?_⟩
      have h' := congrFun (congrFun he' i) j
      rw [Matrix.map_apply, Matrix.map_apply] at h'
      rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, h', sub_self]
  have hφ : ∀ X : Matrix m r A, p' (X.map π) → Xᴴ * H * X - T ∈ hermSub r (RingHom.ker π) →
      ∃ φ : entSub m r 𝔟 →+ Matrix r r A,
        (∀ Y : entSub m r 𝔟, (X + (Y : Matrix m r A))ᴴ * H * (X + (Y : Matrix m r A)) - T =
          Xᴴ * H * X - T + φ Y) ∧
          ∀ S ∈ hermSub r (RingHom.ker π), ∃ Y, φ Y = S := by
    intro X hp hg
    refine ⟨AddMonoidHom.mk' (fun Y => Xᴴ * H * Y.1 + Y.1ᴴ * H * X) (fun Y Z => by
      simp only [AddSubgroup.coe_add, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      abel), fun Y => ?_, fun S hS => ?_⟩
    · have hq := quad_eq_zero h𝔟s h𝔟2 H Y.2
      show _ = _ + (Xᴴ * H * Y.1 + Y.1ᴴ * H * X)
      simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
      rw [hq]
      abel
    · have hk := (mem_hermSub.mp hg).2
      obtain ⟨Y, hY, hYS⟩ := RC X hp (fun i j => by
        have h' := hk i j
        rwa [Matrix.sub_apply] at h' ⊢) S hS
      exact ⟨⟨Y, hY⟩, hYS⟩
  have hu := card_uniform (entSub m r 𝔟) (hermSub r (RingHom.ker π))
    (fun X => Xᴴ * H * X - T) (fun X => p' (X.map π)) (fun X Y hY => hinv X Y hY) hφ
  have hpre := card_preimage f hfs (fun X' => p' X' ∧ X'ᴴ * H.map π * X' = T.map π)
  beta_reduce at hu hpre
  have e1 : Nat.card {X : Matrix m r A // p' (X.map π) ∧ Xᴴ * H * X = T} =
      Nat.card {a : Matrix m r A // p' (a.map π) ∧ aᴴ * H * a - T = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun X => by rw [sub_eq_zero])
  have e2 : Nat.card {a : Matrix m r A //
        p' (a.map π) ∧ aᴴ * H * a - T ∈ hermSub r (RingHom.ker π)} =
      Nat.card {a : Matrix m r A // p' (f a) ∧ (f a)ᴴ * H.map π * f a = T.map π} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [e1, ← hu, e2, hpre, hkerf]
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices
